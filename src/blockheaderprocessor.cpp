#include "blockheaderprocessor.h"
#include "blockannounce.h"
#include "chain.h"
#include "consensus/validation.h"
#include "main.h" // Misbehaving, UpdateBlockAvailability
#include "net.h"
#include "nodestate.h"
#include "primitives/block.h"
#include "util.h"
#include "inflightindex.h"
#include "utilprocessmsg.h" // BlockInFlightMarker
#include <boost/range/adaptor/reversed.hpp>

using namespace std;

/** Maximum number of unconnecting headers announcements before DoS score */
const int MAX_UNCONNECTING_HEADERS = 10;

// Check if header connects with active chain
bool headerConnects(const CBlockHeader& h) {
    return mapBlockIndex.find(h.hashPrevBlock) != mapBlockIndex.end();
}

DefaultHeaderProcessor::DefaultHeaderProcessor(CNode* pfrom,
        InFlightIndex& i,
        ThinBlockManager& mg,
        BlockInFlightMarker& inFlight,
        std::function<void()> checkBlockIndex,
        std::function<void()> sendGetHeaders) :
    pfrom(pfrom), blocksInFlight(i), thinmg(mg), markAsInFlight(inFlight),
    checkBlockIndex(checkBlockIndex), sendGetHeaders(sendGetHeaders)
{
}

// maybeAnnouncement: Header *might* have been received as a block announcement.
bool DefaultHeaderProcessor::operator()(const std::vector<CBlockHeader>& headers,
        bool peerSentMax,
        bool maybeAnnouncement)
{
    if (maybeAnnouncement && !headerConnects(headers.at(0)))
    {
        // Send a getheaders message in response to try to connect the chain.
        // Once a headers message is received that is valid and does connect,
        // nUnconnectingHeaders gets reset back to 0.
        NodeStatePtr(pfrom->id)->unconnectingHeaders++;
        sendGetHeaders();
        UpdateBlockAvailability(pfrom->id, headers.back().GetHash());

        if (NodeStatePtr(pfrom->id)->unconnectingHeaders % MAX_UNCONNECTING_HEADERS == 0)
            Misbehaving(pfrom->id, 20);
        return true;
    }

    bool ok;
    CBlockIndex* pindexLast;
    std::tie(ok, pindexLast) = acceptHeaders(headers);
    if (!ok)
        return false;

    NodeStatePtr(pfrom->id)->unconnectingHeaders = 0;

    if (pindexLast)
        UpdateBlockAvailability(pfrom->GetId(), pindexLast->GetBlockHash());

    if (peerSentMax && pindexLast) {
        // Headers message had its maximum size; the peer may have more headers.
        // TODO: optimize: if pindexLast is an ancestor of chainActive.Tip or pindexBestHeader, continue
        // from there instead.
        LogPrint("block", "send getheaders (%d) to end peer=%d (startheight:%d)\n", pindexLast->nHeight, pfrom->id, pfrom->nStartingHeight);
        pfrom->PushMessage("getheaders", chainActive.GetLocator(pindexLast), uint256());
    }

    if (pindexLast && maybeAnnouncement) {
        std::vector<CBlockIndex*> toFetch = findMissingBlocks(pindexLast);

        // We may or may not start downloading the blocks
        // from this peer now.
        suggestDownload(toFetch, pindexLast);
    }

    checkBlockIndex();
    return true;
}

CBlockIndex* LastCommonAncestor(CBlockIndex* pa, CBlockIndex* pb) {
    if (pa->nHeight > pb->nHeight) {
        pa = pa->GetAncestor(pb->nHeight);
    } else if (pb->nHeight > pa->nHeight) {
        pb = pb->GetAncestor(pa->nHeight);
    }

    while (pa != pb && pa && pb) {
        pa = pa->pprev;
        pb = pb->pprev;
    }

    // Eventually all chain branches meet at the genesis block.
    assert(pa == pb);
    return pa;
}

std::tuple<bool, CBlockIndex*> DefaultHeaderProcessor::acceptHeaders(
        const std::vector<CBlockHeader>& headers) {

    CBlockIndex *pindexLast = nullptr;
    for (const CBlockHeader& header : headers) {
        CValidationState state;
        if (pindexLast != nullptr && header.hashPrevBlock != pindexLast->GetBlockHash()) {
            Misbehaving(pfrom->GetId(), 20);
            return std::make_tuple(
                    error("non-continuous headers sequence"), pindexLast);
        }
        int ret = AcceptBlockHeader(header, state, &pindexLast);
        if (ret == false) {
            int nDoS;
            if (state.IsInvalid(nDoS)) {
                if (nDoS > 0)
                    Misbehaving(pfrom->GetId(), nDoS);
                return std::make_tuple(
                        error("invalid header received"), pindexLast);
            }
        }

        bool fNew = (ret == 2); // AcceptBlockHeader just added it to the block index
        // REBTODO - debug below only if it's new to the BlockIndex within the last 2 minutes
        CBlockIndex *pindexFork = LastCommonAncestor(pindexLast, pindexBestHeader);
        std::string strFork;
        std::string strDesc;
        if (pindexFork->nHeight < pindexLast->nHeight) {
            bool fEqualWork = (pindexLast->nChainWork == pindexBestHeader->nChainWork);
            strFork += strprintf(" %sfork@%d", fEqualWork ? "=" : "", pindexFork->nHeight);
        } else if (pindexLast == chainActive.Tip())
            strDesc += "tip "; // it's the current tip
        else if (pindexLast == pindexBestHeader)
            strDesc += "best "; // it's the current best header
        else if (pindexLast->nChainWork < chainActive.Tip()->nChainWork)
            strDesc += "old "; // it's less work than our current tip
        else if (pindexLast->nTx > 0)
            strDesc += "got "; // we have the full block already
        LogPrint((headers.size() == 1 || fNew || pindexLast->nHeight > pindexBestHeader->nHeight-3) ? "block" : "blockhist", "recv %s%sheader %s (%d%s) peer=%d\n", fNew ? "new " : "", strDesc, pindexLast->GetBlockHash().ToString(), pindexLast->nHeight, strFork, pfrom->id);
    }
    return std::make_tuple(true, pindexLast);
}

std::vector<CBlockIndex*> DefaultHeaderProcessor::findMissingBlocks(CBlockIndex* last) {
    assert(last);

    vector<CBlockIndex*> toFetch;
    CBlockIndex* walk = last;

    // Calculate all the blocks we'd need to switch to last, up to a limit.
    do {
        if (toFetch.size() == MAX_BLOCKS_IN_TRANSIT_PER_PEER)
            break;

        if (chainActive.Contains(walk))
            break;

        if (walk->nStatus & BLOCK_HAVE_DATA)
            continue;

        if (blocksInFlight.isInFlight(walk->GetBlockHash()))
            continue;

        // We don't have this block, and it's not yet in flight.
        toFetch.push_back(walk);

    } while ((walk = walk->pprev));

    return toFetch;
}

bool DefaultHeaderProcessor::hasEqualOrMoreWork(CBlockIndex* last) {
    return last->IsValid(BLOCK_VALID_TREE)
        && chainActive.Tip()->nChainWork <= last->nChainWork;
}

void DefaultHeaderProcessor::suggestDownload(const std::vector<CBlockIndex*>& toFetch, CBlockIndex* last) {
    std::vector<CInv> toGet;

    if (!hasEqualOrMoreWork(last))
        return;

    for (auto b : boost::adaptors::reverse(toFetch)) {

        BlockAnnounceReceiver ann(b->GetBlockHash(),
                *pfrom, thinmg, blocksInFlight);

        // Stop if we don't want to download this block now.
        // Won't want next.
        if (!ann.onBlockAnnounced(toGet, true))
            break;

        // This block has been requested from peer.
        markAsInFlight(pfrom->id, b->GetBlockHash(), Params().GetConsensus(), nullptr);
    }

    if (!toGet.empty()) {
        LogPrint("block", "Downloading blocks toward %s (%d) via headers direct fetch\n",
                last->GetBlockHash().ToString(), last->nHeight);
        pfrom->PushMessage("getdata", toGet);
    }
}
