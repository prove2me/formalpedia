-- Prove2me | Definitions.Def_OAIQ106E139
-- name    : OAIQ106E139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:36:14.691047+00:00
-- url     : https://prove2.me/theorems/6e60f987-cc60-4c8a-9f20-d66137f8b20a
-- title:
--   Definitions bundle OAIQ106E139 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 844 declarations of OpenAI's Lean: 844 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm282`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm283`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm284`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm288`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm289`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm29`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm290`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm291`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm293`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm294`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm295`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm297`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm298`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm299`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm3`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm30`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm300`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm302`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm303`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm304`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm305`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm306`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm307`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm309`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm31`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm311`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm312`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm313`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm314`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm315`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm316`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm317`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTerm318` and 804 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedTargets_ReductionData0`, `MutuallyUnbiased_MixedTargets_ReductionData1`, `MutuallyUnbiased_MixedTargets_ReductionData10`, `MutuallyUnbiased_MixedTargets_ReductionData11`, `MutuallyUnbiased_MixedTargets_ReductionData12`, `MutuallyUnbiased_MixedTargets_ReductionData13`, `MutuallyUnbiased_MixedTargets_ReductionData14`, `MutuallyUnbiased_MixedTargets_ReductionData15`, `MutuallyUnbiased_MixedTargets_ReductionData16`, `MutuallyUnbiased_MixedTargets_ReductionData17`, `MutuallyUnbiased_MixedTargets_ReductionData18`, `MutuallyUnbiased_MixedTargets_ReductionData19`, `MutuallyUnbiased_MixedTargets_ReductionData2`, `MutuallyUnbiased_MixedTargets_ReductionData20`, `MutuallyUnbiased_MixedTargets_ReductionData21`, `MutuallyUnbiased_MixedTargets_ReductionData22`, `MutuallyUnbiased_MixedTargets_ReductionData23`, `MutuallyUnbiased_MixedTargets_ReductionData24`, `MutuallyUnbiased_MixedTargets_ReductionData25`, `MutuallyUnbiased_MixedTargets_ReductionData26`, `MutuallyUnbiased_MixedTargets_ReductionData27`, `MutuallyUnbiased_MixedTargets_ReductionData28`, `MutuallyUnbiased_MixedTargets_ReductionData29`, `MutuallyUnbiased_MixedTargets_ReductionData3`, `MutuallyUnbiased_MixedTargets_ReductionData30`, `MutuallyUnbiased_MixedTargets_ReductionData31`, `MutuallyUnbiased_MixedTargets_ReductionData8`, `MutuallyUnbiased_MixedTargets_ReductionData9`, `MutuallyUnbiased_PairTargets_Assembly`.
--
--   **Imports.** It imports the bundle `OAIQ106E043` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e` and `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`; the proofs of `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval716_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.family_size_le_five_e`, `OAI.MUB6.fourier_and_family_bound` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm3 : Integer.Sparse Master := [(Sum.inl 0, 2212213202121129984000), (Sum.inl 1, 4147899753977118720000), (Sum.inl 2, -1382633251325706240000)]

def reducedTerm4 : Integer.Sparse Master := [(Sum.inl 0, 7396337533618446336000), (Sum.inl 1, -6723943212380405760000), (Sum.inl 2, 3361971606190202880000)]

def reducedTerm5 : Integer.Sparse Master := [(Sum.inl 0, 1692420459861196800000), (Sum.inl 1, -1692420459861196800000)]

def reducedTerm6 : Integer.Sparse Master := [(Sum.inl 0, 1316966819005071360000), (Sum.inl 1, 6584834095025356800000)]

def reducedTerm7 : Integer.Sparse Master := [(Sum.inl 0, 1737686641551114240000), (Sum.inl 1, 457285958302924800000)]

def reducedTerm8 : Integer.Sparse Master := [(Sum.inl 0, -8075576528732160000), (Sum.inl 1, 2523617665228800000), (Sum.inl 2, 30283411982745600000), (Sum.inl 5, -151417059913728000000), (Sum.inl 6, 30283411982745600000), (Sum.inl 7, 242267295861964800000), (Sum.inl 9, -100944706609152000000), (Sum.inl 35, 121133647930982400000), (Sum.inl 58, 2523617665228800000), (Sum.inl 69, 363400943792947200000), (Sum.inl 70, 323023061149286400000), (Sum.inl 71, 242267295861964800000), (Sum.inl 257, 80755765287321600000)]

def reducedTerm9 : Integer.Sparse Master := [(Sum.inl 0, 8075576528732160000), (Sum.inl 1, 7570852995686400000), (Sum.inl 2, -7570852995686400000), (Sum.inl 5, -40377882643660800000), (Sum.inl 6, 20188941321830400000), (Sum.inl 9, -60566823965491200000), (Sum.inl 58, 5047235330457600000), (Sum.inl 69, 40377882643660800000), (Sum.inl 70, 40377882643660800000), (Sum.inl 71, 80755765287321600000)]

def reducedTerm29 : Integer.Sparse Master := [(Sum.inl 0, -34488646944030720000), (Sum.inl 1, 86221617360076800000), (Sum.inl 2, 71851347800064000000), (Sum.inl 6, -28740539120025600000), (Sum.inl 9, 57481078240051200000), (Sum.inl 35, 229924312960204800000), (Sum.inl 58, -14370269560012800000), (Sum.inl 257, 229924312960204800000), (Sum.inl 495, 229924312960204800000)]

def reducedTerm30 : Integer.Sparse Master := [(Sum.inl 0, -71713207222272000000), (Sum.inl 1, -268924527083520000000), (Sum.inl 2, 89641509027840000000), (Sum.inl 5, 119522012037120000000), (Sum.inl 7, 478088048148480000000), (Sum.inl 9, 239044024074240000000), (Sum.inl 69, 478088048148480000000), (Sum.inl 70, 478088048148480000000)]

def reducedTerm31 : Integer.Sparse Master := [(Sum.inl 0, -9416232821882880000), (Sum.inl 2, -6725880587059200000), (Sum.inl 5, 13451761174118400000), (Sum.inl 8, 53807044696473600000), (Sum.inl 9, 26903522348236800000), (Sum.inl 71, 107614089392947200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm32 : Integer.Sparse Master := [(Sum.inl 0, 56064988705259520000), (Sum.inl 1, 210243707644723200000), (Sum.inl 2, -70081235881574400000), (Sum.inl 5, -280324943526297600000), (Sum.inl 6, -70081235881574400000), (Sum.inl 9, -280324943526297600000), (Sum.inl 58, -70081235881574400000)]

def reducedTerm33 : Integer.Sparse Master := [(Sum.inl 0, 14475351711744000000), (Sum.inl 1, -32898526617600000000), (Sum.inl 2, -13159410647040000000), (Sum.inl 5, -26318821294080000000), (Sum.inl 9, -52637642588160000000), (Sum.inl 256, 315825855528960000000)]

def reducedTerm34 : Integer.Sparse Master := [(Sum.inl 0, 34488646944030720000), (Sum.inl 1, -86221617360076800000), (Sum.inl 2, -86221617360076800000), (Sum.inl 6, -43110808680038400000), (Sum.inl 58, -43110808680038400000), (Sum.inl 495, 689772938880614400000)]

def reducedTerm35 : Integer.Sparse Master := [(Sum.inl 0, 59622898047713280000), (Sum.inl 1, 298114490238566400000), (Sum.inl 2, 298114490238566400000), (Sum.inl 9, 298114490238566400000), (Sum.inl 70, 1192457960954265600000)]

def reducedTerm36 : Integer.Sparse Master := [(Sum.inl 0, -36132050781388800000), (Sum.inl 1, 72264101562777600000), (Sum.inl 2, 36132050781388800000), (Sum.inl 9, -144528203125555200000), (Sum.inl 71, -578112812502220800000)]

def reducedTerm37 : Integer.Sparse Master := [(Sum.inl 0, 30950708101447680000), (Sum.inl 1, 116065155380428800000), (Sum.inl 2, -38688385126809600000), (Sum.inl 9, 154753540507238400000), (Sum.inl 69, 619014162028953600000)]

def reducedTerm38 : Integer.Sparse Master := [(Sum.inl 0, 4530669832765440000), (Sum.inl 1, -5663337290956800000), (Sum.inl 2, 16990011872870400000), (Sum.inl 9, 22653349163827200000), (Sum.inl 257, 90613396655308800000)]

def reducedTerm39 : Integer.Sparse Master := [(Sum.inl 0, -5074358038364160000), (Sum.inl 1, -25371790191820800000), (Sum.inl 2, -25371790191820800000), (Sum.inl 9, -101487160767283200000), (Sum.inl 58, -25371790191820800000)]

def reducedTerm40 : Integer.Sparse Master := [(Sum.inl 0, -243162140175360000000), (Sum.inl 2, -115791495321600000000), (Sum.inl 3, 1852663925145600000000), (Sum.inl 5, -2084246915788800000000), (Sum.inl 6, 231582990643200000000), (Sum.inl 7, 926331962572800000000), (Sum.inl 9, -694748971929600000000), (Sum.inl 13, 3705327850291200000000), (Sum.inl 35, 7410655700582400000000), (Sum.inl 52, 7410655700582400000000), (Sum.inl 58, 57895747660800000000), (Sum.inl 60, 4631659812864000000000), (Sum.inl 69, 926331962572800000000), (Sum.inl 70, 926331962572800000000), (Sum.inl 128, 3705327850291200000000), (Sum.inl 257, 1852663925145600000000), (Sum.inl 260, -2778995887718400000000), (Sum.inl 495, 2778995887718400000000)]

def reducedTerm41 : Integer.Sparse Master := [(Sum.inl 0, -51013001539584000000), (Sum.inl 1, -178545505388544000000), (Sum.inl 2, -204052006158336000000), (Sum.inl 5, 204052006158336000000), (Sum.inl 9, 102026003079168000000), (Sum.inl 52, -408104012316672000000), (Sum.inl 58, -25506500769792000000), (Sum.inl 128, -408104012316672000000), (Sum.inl 495, -408104012316672000000)]

def reducedTerm42 : Integer.Sparse Master := [(Sum.inl 0, 53094867207782400000), (Sum.inl 1, 12067015274496000000), (Sum.inl 2, 12067015274496000000), (Sum.inl 5, -144804183293952000000), (Sum.inl 6, 24134030548992000000), (Sum.inl 7, 193072244391936000000), (Sum.inl 9, -96536122195968000000), (Sum.inl 35, 386144488783872000000), (Sum.inl 52, 193072244391936000000), (Sum.inl 60, 193072244391936000000), (Sum.inl 69, 193072244391936000000), (Sum.inl 70, 193072244391936000000), (Sum.inl 257, 193072244391936000000), (Sum.inl 260, -579216733175808000000)]

def reducedTerm43 : Integer.Sparse Master := [(Sum.inl 0, 91088120335564800000), (Sum.inl 1, -49236821803008000000), (Sum.inl 2, -172328876310528000000), (Sum.inl 5, 590841861636096000000), (Sum.inl 6, -73855232704512000000), (Sum.inl 8, -787789148848128000000), (Sum.inl 9, -196947287212032000000), (Sum.inl 52, -393894574424064000000), (Sum.inl 58, 12309205450752000000), (Sum.inl 69, -196947287212032000000), (Sum.inl 71, -787789148848128000000)]

def reducedTerm44 : Integer.Sparse Master := [(Sum.inl 0, -57327776686817280000), (Sum.inl 1, 39536397715046400000), (Sum.inl 2, 217450187432755200000), (Sum.inl 3, 948873545161113600000), (Sum.inl 5, -474436772580556800000), (Sum.inl 6, 59304596572569600000), (Sum.inl 7, 948873545161113600000), (Sum.inl 9, 158145590860185600000), (Sum.inl 35, 948873545161113600000), (Sum.inl 52, 948873545161113600000), (Sum.inl 58, -9884099428761600000), (Sum.inl 69, 474436772580556800000), (Sum.inl 70, 316291181720371200000)]

def reducedTerm45 : Integer.Sparse Master := [(Sum.inl 0, -35582757943541760000), (Sum.inl 1, -52715196953395200000), (Sum.inl 2, -118609193145139200000), (Sum.inl 5, 105430393906790400000), (Sum.inl 6, -39536397715046400000), (Sum.inl 52, -210860787813580800000), (Sum.inl 58, 6589399619174400000), (Sum.inl 69, -105430393906790400000)]

def reducedTerm46 : Integer.Sparse Master := [(Sum.inl 0, 59296244178124800000), (Sum.inl 1, -13476419131392000000), (Sum.inl 2, 13476419131392000000), (Sum.inl 3, 215622706102272000000), (Sum.inl 5, 53905676525568000000), (Sum.inl 6, 40429257394176000000), (Sum.inl 9, 53905676525568000000), (Sum.inl 13, 215622706102272000000), (Sum.inl 35, 646868118306816000000), (Sum.inl 52, 431245412204544000000), (Sum.inl 58, -13476419131392000000), (Sum.inl 60, 431245412204544000000), (Sum.inl 128, 215622706102272000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 495, 215622706102272000000)]

def reducedTerm47 : Integer.Sparse Master := [(Sum.inl 0, 16465679651635200000), (Sum.inl 1, -41164199129088000000), (Sum.inl 2, -27442799419392000000), (Sum.inl 3, 43908479071027200000), (Sum.inl 5, -21954239535513600000), (Sum.inl 6, -2744279941939200000), (Sum.inl 7, 87816958142054400000), (Sum.inl 9, 21954239535513600000), (Sum.inl 35, 87816958142054400000), (Sum.inl 52, 43908479071027200000), (Sum.inl 69, 43908479071027200000), (Sum.inl 70, 43908479071027200000)]

def reducedTerm48 : Integer.Sparse Master := [(Sum.inl 0, -83702597065113600000), (Sum.inl 1, -196947287212032000000), (Sum.inl 2, -123092054507520000000), (Sum.inl 5, 196947287212032000000), (Sum.inl 8, -393894574424064000000), (Sum.inl 9, -98473643606016000000), (Sum.inl 71, -393894574424064000000)]

def reducedTerm49 : Integer.Sparse Master := [(Sum.inl 0, -17893337127321600000), (Sum.inl 1, 41751119963750400000), (Sum.inl 2, 29822228545536000000), (Sum.inl 5, -47715565672857600000), (Sum.inl 6, 23857782836428800000), (Sum.inl 9, -23857782836428800000), (Sum.inl 58, -5964445709107200000)]

def reducedTerm50 : Integer.Sparse Master := [(Sum.inl 0, 25561807165440000000), (Sum.inl 1, -25561807165440000000), (Sum.inl 2, 136329638215680000000), (Sum.inl 5, -34082409553920000000), (Sum.inl 9, -34082409553920000000), (Sum.inl 35, -136329638215680000000), (Sum.inl 70, -136329638215680000000)]

def reducedTerm51 : Integer.Sparse Master := [(Sum.inl 0, -14354097769267200000), (Sum.inl 1, 33492894794956800000), (Sum.inl 2, 14354097769267200000), (Sum.inl 6, -4784699256422400000), (Sum.inl 9, 19138797025689600000), (Sum.inl 52, 76555188102758400000), (Sum.inl 69, 76555188102758400000)]

def reducedTerm52 : Integer.Sparse Master := [(Sum.inl 0, 2611509059174400000), (Sum.inl 1, 3561148717056000000), (Sum.inl 2, 17805743585280000000), (Sum.inl 5, -4748198289408000000), (Sum.inl 6, 1187049572352000000), (Sum.inl 9, -4748198289408000000), (Sum.inl 35, -18992793157632000000), (Sum.inl 60, -18992793157632000000), (Sum.inl 257, -18992793157632000000)]

def reducedTerm53 : Integer.Sparse Master := [(Sum.inl 0, 7382985781248000000), (Sum.inl 1, -18457464453120000000), (Sum.inl 2, -11745659197440000000), (Sum.inl 5, -6711805255680000000), (Sum.inl 6, -3355902627840000000), (Sum.inl 7, 26847221022720000000), (Sum.inl 9, 13423610511360000000), (Sum.inl 35, 26847221022720000000), (Sum.inl 54, -80541663068160000000), (Sum.inl 259, -80541663068160000000), (Sum.inl 260, -80541663068160000000)]

def reducedTerm54 : Integer.Sparse Master := [(Sum.inl 0, -7382985781248000000), (Sum.inl 1, 16779513139200000000), (Sum.inl 2, 3355902627840000000), (Sum.inl 5, 13423610511360000000), (Sum.inl 6, -3355902627840000000), (Sum.inl 9, 13423610511360000000), (Sum.inl 259, -161083326136320000000)]

def reducedTerm55 : Integer.Sparse Master := [(Sum.inl 0, -34488646944030720000), (Sum.inl 1, 86221617360076800000), (Sum.inl 2, 71851347800064000000), (Sum.inl 5, 57481078240051200000), (Sum.inl 6, -14370269560012800000), (Sum.inl 9, 57481078240051200000), (Sum.inl 260, -689772938880614400000)]

def reducedTerm56 : Integer.Sparse Master := [(Sum.inl 0, 164861191898726400000), (Sum.inl 1, 618229469620224000000), (Sum.inl 2, 123645893924044800000), (Sum.inl 5, -329722383797452800000), (Sum.inl 6, -164861191898726400000), (Sum.inl 13, 659444767594905600000), (Sum.inl 35, 1318889535189811200000), (Sum.inl 52, 1318889535189811200000), (Sum.inl 60, 1318889535189811200000), (Sum.inl 128, 659444767594905600000)]

def reducedTerm57 : Integer.Sparse Master := [(Sum.inl 0, 84373900911820800000), (Sum.inl 1, 253121702735462400000), (Sum.inl 2, 84373900911820800000), (Sum.inl 5, 337495603647283200000), (Sum.inl 6, 421869504559104000000), (Sum.inl 128, -674991207294566400000)]

def reducedTerm58 : Integer.Sparse Master := [(Sum.inl 0, 79685238097059840000), (Sum.inl 1, -43073101674086400000), (Sum.inl 2, -236902059207475200000), (Sum.inl 3, -344584813392691200000), (Sum.inl 5, 689169626785382400000), (Sum.inl 6, -118451029603737600000), (Sum.inl 7, -172292406696345600000), (Sum.inl 8, -344584813392691200000), (Sum.inl 35, -344584813392691200000), (Sum.inl 52, -689169626785382400000)]

def reducedTerm59 : Integer.Sparse Master := [(Sum.inl 0, -230151142757007360000), (Sum.inl 1, -609223613180313600000), (Sum.inl 2, -541532100604723200000), (Sum.inl 5, 812298150907084800000), (Sum.inl 6, -135383025151180800000), (Sum.inl 8, -541532100604723200000), (Sum.inl 52, -541532100604723200000)]

def reducedTerm60 : Integer.Sparse Master := [(Sum.inl 0, 35582757943541760000), (Sum.inl 1, 26357598476697600000), (Sum.inl 2, 92251594668441600000), (Sum.inl 3, 210860787813580800000), (Sum.inl 5, -105430393906790400000), (Sum.inl 6, 19768198857523200000), (Sum.inl 7, 105430393906790400000), (Sum.inl 35, 210860787813580800000), (Sum.inl 52, 210860787813580800000)]

def reducedTerm61 : Integer.Sparse Master := [(Sum.inl 0, 55350956801064960000), (Sum.inl 1, -39536397715046400000), (Sum.inl 2, -79072795430092800000), (Sum.inl 5, 79072795430092800000), (Sum.inl 6, -79072795430092800000), (Sum.inl 52, -316291181720371200000)]

def reducedTerm62 : Integer.Sparse Master := [(Sum.inl 0, -11373614787870720000), (Sum.inl 2, 20679299614310400000), (Sum.inl 6, 15509474710732800000), (Sum.inl 35, 82717198457241600000), (Sum.inl 52, 82717198457241600000), (Sum.inl 60, 82717198457241600000)]

def reducedTerm63 : Integer.Sparse Master := [(Sum.inl 0, 105460574142873600000), (Sum.inl 1, -246074673000038400000), (Sum.inl 2, -140614098857164800000), (Sum.inl 5, 562456395428659200000), (Sum.inl 7, -562456395428659200000), (Sum.inl 35, -562456395428659200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm320 : Integer.Sparse Master := [(Sum.inl 0, 12797568867041280000), (Sum.inl 1, -31993922167603200000), (Sum.inl 2, -31993922167603200000), (Sum.inl 27, 63987844335206400000), (Sum.inl 65, 255951377340825600000)]

def reducedTerm321 : Integer.Sparse Master := [(Sum.inl 0, 240879894081361920000), (Sum.inl 1, -354235138354944000000), (Sum.inl 2, 566776221367910400000), (Sum.inl 3, 3400657328207462400000), (Sum.inl 4, 1133552442735820800000), (Sum.inl 12, 1133552442735820800000), (Sum.inl 13, 1133552442735820800000), (Sum.inl 26, 1133552442735820800000), (Sum.inl 33, -3400657328207462400000), (Sum.inl 34, 1133552442735820800000)]

def reducedTerm322 : Integer.Sparse Master := [(Sum.inl 0, -234986432176742400000), (Sum.inl 1, 822452512618598400000), (Sum.inl 2, 117493216088371200000), (Sum.inl 33, -5639674372241817600000)]

def reducedTerm323 : Integer.Sparse Master := [(Sum.inl 0, 30123271749795840000), (Sum.inl 1, 328617509997772800000), (Sum.inl 2, 41077188749721600000), (Sum.inl 3, 657235019995545600000), (Sum.inl 12, 657235019995545600000), (Sum.inl 13, 438156679997030400000)]

def reducedTerm324 : Integer.Sparse Master := [(Sum.inl 0, -373751665957232640000), (Sum.inl 1, -1189209846227558400000), (Sum.inl 2, 339774241779302400000), (Sum.inl 3, 2718193934234419200000), (Sum.inl 12, 2718193934234419200000), (Sum.inl 13, 2718193934234419200000)]

def reducedTerm325 : Integer.Sparse Master := [(Sum.inl 0, 2273983281561600000), (Sum.inl 1, 6821949844684800000), (Sum.inl 2, 4547966563123200000), (Sum.inl 27, 13643899689369600000), (Sum.inl 66, 54575598757478400000)]

def reducedTerm326 : Integer.Sparse Master := [(Sum.inl 0, -37628045307740160000), (Sum.inl 1, 28944650236723200000), (Sum.inl 2, -43416975355084800000), (Sum.inl 3, 231557201893785600000), (Sum.inl 4, 231557201893785600000), (Sum.inl 26, 231557201893785600000)]

def reducedTerm327 : Integer.Sparse Master := [(Sum.inl 0, 64006336235520000000), (Sum.inl 1, -192019008706560000000), (Sum.inl 2, -128012672471040000000), (Sum.inl 26, 1024101379768320000000)]

def reducedTerm328 : Integer.Sparse Master := [(Sum.inl 0, -562281845852160000000), (Sum.inl 1, -3255315949670400000000), (Sum.inl 2, -147968906803200000000), (Sum.inl 3, 2367502508851200000000)]

def reducedTerm329 : Integer.Sparse Master := []

def reducedTerm330 : Integer.Sparse Master := []

def reducedTerm331 : Integer.Sparse Master := []

def reducedTerm332 : Integer.Sparse Master := [(Sum.inl 0, 520756374310502400000), (Sum.inl 1, 1041512748621004800000), (Sum.inl 2, -520756374310502400000), (Sum.inl 3, 8332101988968038400000)]

def reducedTerm333 : Integer.Sparse Master := [(Sum.inl 0, -85307624618065920000), (Sum.inl 1, 319903592317747200000), (Sum.inl 2, 319903592317747200000), (Sum.inl 34, -1706152492361318400000)]

def reducedTerm334 : Integer.Sparse Master := []

def reducedTerm335 : Integer.Sparse Master := [(Sum.inl 0, -119491913318400000), (Sum.inl 1, -33192198144000000), (Sum.inl 2, -99576594432000000), (Sum.inl 5, 132768792576000000), (Sum.inl 31, -796612755456000000), (Sum.inl 51, -1593225510912000000), (Sum.inl 68, -796612755456000000), (Sum.inl 124, -796612755456000000), (Sum.inl 126, -1593225510912000000), (Sum.inl 236, -796612755456000000)]

def reducedTerm336 : Integer.Sparse Master := [(Sum.inl 0, 83531314871746560000), (Sum.inl 1, 30937524026572800000), (Sum.inl 2, 139218858119577600000), (Sum.inl 3, -990000768850329600000), (Sum.inl 4, -247500192212582400000), (Sum.inl 5, -185625144159436800000), (Sum.inl 7, -495000384425164800000), (Sum.inl 12, -247500192212582400000), (Sum.inl 23, 1485001153275494400000), (Sum.inl 24, 1485001153275494400000), (Sum.inl 51, 742500576637747200000), (Sum.inl 55, 1485001153275494400000), (Sum.inl 68, 742500576637747200000), (Sum.inl 124, 742500576637747200000), (Sum.inl 125, 742500576637747200000), (Sum.inl 126, 742500576637747200000), (Sum.inl 197, 742500576637747200000)]

def reducedTerm337 : Integer.Sparse Master := [(Sum.inl 0, 15974757792000000000), (Sum.inl 1, 74548869696000000000), (Sum.inl 2, 47924273376000000000), (Sum.inl 3, -170397416448000000000), (Sum.inl 4, -85198708224000000000), (Sum.inl 5, -85198708224000000000), (Sum.inl 12, -85198708224000000000), (Sum.inl 27, 63899031168000000000), (Sum.inl 31, 255596124672000000000), (Sum.inl 51, 511192249344000000000), (Sum.inl 55, 255596124672000000000), (Sum.inl 68, 255596124672000000000), (Sum.inl 194, -511192249344000000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -511192249344000000000)]

def reducedTerm338 : Integer.Sparse Master := [(Sum.inl 0, 284257613896704000000), (Sum.inl 1, -236881344913920000000), (Sum.inl 2, 1184406724569600000000), (Sum.inl 3, -1263367172874240000000), (Sum.inl 5, -1263367172874240000000), (Sum.inl 12, -1263367172874240000000), (Sum.inl 23, 7580203037245440000000), (Sum.inl 24, 3790101518622720000000), (Sum.inl 25, 3790101518622720000000), (Sum.inl 27, 947525379655680000000), (Sum.inl 54, 3790101518622720000000), (Sum.inl 55, 3790101518622720000000), (Sum.inl 68, 3790101518622720000000), (Sum.inl 195, -7580203037245440000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 487, -7580203037245440000000)]

def reducedTerm339 : Integer.Sparse Master := [(Sum.inl 0, 14000347684915200000), (Sum.inl 1, 120002980156416000000), (Sum.inl 2, -50001241731840000000), (Sum.inl 23, 480011920625664000000), (Sum.inl 24, 960023841251328000000), (Sum.inl 27, -240005960312832000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 55, 480011920625664000000), (Sum.inl 194, -480011920625664000000)]

def reducedTerm340 : Integer.Sparse Master := [(Sum.inl 0, 68634108297216000000), (Sum.inl 2, -102951162445824000000), (Sum.inl 3, -411804649783296000000), (Sum.inl 5, 137268216594432000000), (Sum.inl 7, -137268216594432000000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -137268216594432000000), (Sum.inl 23, 411804649783296000000), (Sum.inl 24, 411804649783296000000), (Sum.inl 27, -308853487337472000000), (Sum.inl 55, 411804649783296000000)]

def reducedTerm341 : Integer.Sparse Master := [(Sum.inl 0, -156293927090380800000), (Sum.inl 1, 347319837978624000000), (Sum.inl 2, -86829959494656000000), (Sum.inl 23, 1389279351914496000000), (Sum.inl 24, 1389279351914496000000), (Sum.inl 27, -1041959513935872000000), (Sum.inl 55, 1389279351914496000000)]

def reducedTerm342 : Integer.Sparse Master := [(Sum.inl 0, 505877359067136000000), (Sum.inl 1, 903352426905600000000), (Sum.inl 2, -180670485381120000000), (Sum.inl 3, -10117547181342720000000), (Sum.inl 4, -1445363883048960000000), (Sum.inl 5, 361340970762240000000), (Sum.inl 12, -5781455532195840000000), (Sum.inl 13, -7226819415244800000000), (Sum.inl 27, -1084022912286720000000), (Sum.inl 33, 8672183298293760000000), (Sum.inl 51, 4336091649146880000000), (Sum.inl 55, 4336091649146880000000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 194, -8672183298293760000000)]

def reducedTerm343 : Integer.Sparse Master := [(Sum.inl 0, -242232654988800000000), (Sum.inl 1, 484465309977600000000), (Sum.inl 2, -242232654988800000000), (Sum.inl 27, -1453395929932800000000), (Sum.inl 194, -5813583719731200000000)]

def reducedTerm344 : Integer.Sparse Master := [(Sum.inl 0, 37201146819379200000), (Sum.inl 2, 48948877393920000000), (Sum.inl 3, -234954611490816000000), (Sum.inl 4, -156636407660544000000), (Sum.inl 5, -39159101915136000000), (Sum.inl 12, -78318203830272000000), (Sum.inl 27, 58738652872704000000), (Sum.inl 31, 469909222981632000000), (Sum.inl 51, 469909222981632000000), (Sum.inl 55, 234954611490816000000)]

def reducedTerm345 : Integer.Sparse Master := [(Sum.inl 0, -34148041482240000000), (Sum.inl 1, 29269749841920000000), (Sum.inl 2, -4878291640320000000), (Sum.inl 5, -19513166561280000000), (Sum.inl 31, 234157998735360000000), (Sum.inl 51, 234157998735360000000)]

def reducedTerm346 : Integer.Sparse Master := [(Sum.inl 0, -360250597856378880000), (Sum.inl 1, 900626494640947200000), (Sum.inl 2, 128660927805849600000), (Sum.inl 3, -2058574844893593600000), (Sum.inl 4, -1029287422446796800000), (Sum.inl 5, -257321855611699200000), (Sum.inl 12, -1029287422446796800000), (Sum.inl 27, 771965566835097600000), (Sum.inl 51, 3087862267340390400000), (Sum.inl 55, 3087862267340390400000)]

def reducedTerm347 : Integer.Sparse Master := [(Sum.inl 0, -53505487723806720000), (Sum.inl 1, -280266840458035200000), (Sum.inl 2, -140133420229017600000), (Sum.inl 3, 815321717696102400000), (Sum.inl 5, 203830429424025600000), (Sum.inl 7, 407660858848051200000), (Sum.inl 12, 407660858848051200000), (Sum.inl 23, -1222982576544153600000), (Sum.inl 25, -611491288272076800000), (Sum.inl 27, -305745644136038400000), (Sum.inl 54, -1222982576544153600000), (Sum.inl 68, -611491288272076800000), (Sum.inl 124, -611491288272076800000), (Sum.inl 125, -1222982576544153600000), (Sum.inl 196, -611491288272076800000)]

def reducedTerm348 : Integer.Sparse Master := [(Sum.inl 0, -19621061271060480000), (Sum.inl 1, 17837328428236800000), (Sum.inl 2, -8918664214118400000), (Sum.inl 23, -428095882277683200000), (Sum.inl 24, -428095882277683200000), (Sum.inl 55, -856191764555366400000), (Sum.inl 63, -428095882277683200000), (Sum.inl 65, -428095882277683200000)]

def reducedTerm349 : Integer.Sparse Master := [(Sum.inl 0, -310919531112529920000), (Sum.inl 1, -115155381893529600000), (Sum.inl 2, 172733072840294400000), (Sum.inl 3, 5527458330889420800000), (Sum.inl 4, 921243055148236800000), (Sum.inl 5, -230310763787059200000), (Sum.inl 7, 921243055148236800000), (Sum.inl 12, 2763729165444710400000), (Sum.inl 23, -5527458330889420800000), (Sum.inl 25, -5527458330889420800000), (Sum.inl 26, 921243055148236800000), (Sum.inl 27, 690932291361177600000), (Sum.inl 33, -5527458330889420800000), (Sum.inl 51, -2763729165444710400000), (Sum.inl 54, -5527458330889420800000), (Sum.inl 55, -2763729165444710400000), (Sum.inl 63, -2763729165444710400000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -2763729165444710400000)]

def reducedTerm350 : Integer.Sparse Master := [(Sum.inl 0, -157505859315302400000), (Sum.inl 1, 147661743108096000000), (Sum.inl 2, -442985229324288000000), (Sum.inl 3, 2362587889729536000000), (Sum.inl 4, 1181293944864768000000), (Sum.inl 5, 295323486216192000000), (Sum.inl 12, 787529296576512000000), (Sum.inl 23, -1181293944864768000000), (Sum.inl 25, -2362587889729536000000), (Sum.inl 26, 787529296576512000000), (Sum.inl 27, -885970458648576000000), (Sum.inl 31, -1181293944864768000000), (Sum.inl 33, -2362587889729536000000), (Sum.inl 54, -2362587889729536000000), (Sum.inl 65, -1181293944864768000000), (Sum.inl 195, 2362587889729536000000)]

def reducedTerm351 : Integer.Sparse Master := [(Sum.inl 0, -268906834053365760000), (Sum.inl 1, -1110702140655206400000), (Sum.inl 2, 116916014805811200000), (Sum.inl 3, -935328118446489600000), (Sum.inl 5, -233832029611622400000), (Sum.inl 12, -935328118446489600000), (Sum.inl 23, 2805984355339468800000), (Sum.inl 25, 2805984355339468800000), (Sum.inl 27, 701496088834867200000), (Sum.inl 54, 2805984355339468800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm352 : Integer.Sparse Master := [(Sum.inl 0, 56011331677593600000), (Sum.inl 1, -76379088651264000000), (Sum.inl 5, 50919392434176000000), (Sum.inl 27, -152758177302528000000), (Sum.inl 195, 1222065418420224000000)]

def reducedTerm353 : Integer.Sparse Master := [(Sum.inl 0, -14658610686935040000), (Sum.inl 1, -3857529128140800000), (Sum.inl 2, -15430116512563200000), (Sum.inl 3, 246881864201011200000), (Sum.inl 4, 123440932100505600000), (Sum.inl 5, 23145174768844800000), (Sum.inl 7, 92580699075379200000), (Sum.inl 12, 61720466050252800000), (Sum.inl 23, -92580699075379200000), (Sum.inl 24, -185161398150758400000), (Sum.inl 27, -69435524306534400000)]

def reducedTerm354 : Integer.Sparse Master := [(Sum.inl 0, 237855124684800000000), (Sum.inl 1, 951420498739200000000), (Sum.inl 2, -79285041561600000000), (Sum.inl 3, 1268560664985600000000), (Sum.inl 5, 158570083123200000000), (Sum.inl 7, 634280332492800000000), (Sum.inl 12, 634280332492800000000), (Sum.inl 23, -1902840997478400000000), (Sum.inl 27, -475710249369600000000)]

def reducedTerm355 : Integer.Sparse Master := [(Sum.inl 0, 22174662903644160000), (Sum.inl 1, -59701015509811200000), (Sum.inl 2, -5685811000934400000), (Sum.inl 3, 90972976014950400000), (Sum.inl 4, 45486488007475200000), (Sum.inl 5, 11371622001868800000), (Sum.inl 7, 45486488007475200000), (Sum.inl 24, -136459464022425600000), (Sum.inl 27, -34114866005606400000)]

def reducedTerm356 : Integer.Sparse Master := [(Sum.inl 0, 143555146664509440000), (Sum.inl 1, 1435551466645094400000), (Sum.inl 23, 2871102933290188800000), (Sum.inl 27, 717775733322547200000)]

def reducedTerm357 : Integer.Sparse Master := [(Sum.inl 0, 164024766063083520000), (Sum.inl 1, -273374610105139200000), (Sum.inl 24, 2186996880841113600000), (Sum.inl 27, 546749220210278400000)]

def reducedTerm358 : Integer.Sparse Master := [(Sum.inl 0, 69912227813621760000), (Sum.inl 1, 126230411330150400000), (Sum.inl 2, -19420063281561600000), (Sum.inl 3, -1087523543767449600000), (Sum.inl 4, -466081518757478400000), (Sum.inl 5, -77680253126246400000), (Sum.inl 6, 9710031640780800000), (Sum.inl 12, -466081518757478400000), (Sum.inl 13, -466081518757478400000), (Sum.inl 26, -155360506252492800000), (Sum.inl 27, 116520379689369600000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 466081518757478400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 55, 466081518757478400000)]

def reducedTerm359 : Integer.Sparse Master := [(Sum.inl 0, 23951411380592640000), (Sum.inl 1, -6473354427187200000), (Sum.inl 2, 12946708854374400000), (Sum.inl 3, -466081518757478400000), (Sum.inl 4, -207147341669990400000), (Sum.inl 5, -25893417708748800000), (Sum.inl 6, 3236677213593600000), (Sum.inl 7, -51786835417497600000), (Sum.inl 12, -103573670834995200000), (Sum.inl 23, 155360506252492800000), (Sum.inl 25, 310721012504985600000), (Sum.inl 26, -207147341669990400000), (Sum.inl 27, 38840126563123200000), (Sum.inl 35, -51786835417497600000), (Sum.inl 54, 155360506252492800000)]

def reducedTerm360 : Integer.Sparse Master := [(Sum.inl 0, -506151719861760000000), (Sum.inl 1, -683988810624000000000), (Sum.inl 3, 8755056775987200000000), (Sum.inl 4, 2188764193996800000000), (Sum.inl 5, 547191048499200000000), (Sum.inl 6, -68398881062400000000), (Sum.inl 12, 5471910484992000000000), (Sum.inl 13, 2188764193996800000000), (Sum.inl 23, -3283146290995200000000), (Sum.inl 25, -6566292581990400000000), (Sum.inl 27, -820786572748800000000), (Sum.inl 31, -3283146290995200000000), (Sum.inl 33, -13132585163980800000000), (Sum.inl 54, -6566292581990400000000), (Sum.inl 62, -3283146290995200000000)]

def reducedTerm361 : Integer.Sparse Master := [(Sum.inl 0, 7605133555138560000), (Sum.inl 1, 49116487543603200000), (Sum.inl 2, -6337611295948800000), (Sum.inl 3, -50700890367590400000), (Sum.inl 5, -12675222591897600000), (Sum.inl 6, 1584402823987200000), (Sum.inl 7, -25350445183795200000), (Sum.inl 12, -25350445183795200000), (Sum.inl 13, -76051335551385600000), (Sum.inl 23, 76051335551385600000), (Sum.inl 25, 76051335551385600000), (Sum.inl 27, 19012833887846400000), (Sum.inl 35, -25350445183795200000), (Sum.inl 54, 76051335551385600000)]

def reducedTerm362 : Integer.Sparse Master := [(Sum.inl 0, 4259935411200000000), (Sum.inl 1, -101173466016000000000), (Sum.inl 2, 26624596320000000000), (Sum.inl 3, 340794832896000000000), (Sum.inl 4, 170397416448000000000), (Sum.inl 12, 170397416448000000000), (Sum.inl 13, 85198708224000000000)]

def reducedTerm363 : Integer.Sparse Master := [(Sum.inl 0, 10357367083499520000), (Sum.inl 1, 187727278388428800000), (Sum.inl 2, -45313480990310400000), (Sum.inl 3, -828589366679961600000), (Sum.inl 4, -207147341669990400000), (Sum.inl 12, -414294683339980800000), (Sum.inl 13, -310721012504985600000)]

def reducedTerm364 : Integer.Sparse Master := [(Sum.inl 0, -555506660324044800000), (Sum.inl 1, -1666519980972134400000), (Sum.inl 3, 17776213130369433600000), (Sum.inl 4, 2962702188394905600000), (Sum.inl 12, 8888106565184716800000), (Sum.inl 13, 17776213130369433600000), (Sum.inl 32, 1481351094197452800000)]

def reducedTerm365 : Integer.Sparse Master := []

def reducedTerm366 : Integer.Sparse Master := []

def reducedTerm367 : Integer.Sparse Master := []

def reducedTerm368 : Integer.Sparse Master := [(Sum.inl 0, 645605482874204160000), (Sum.inl 1, -3521484452041113600000), (Sum.inl 2, 880371113010278400000), (Sum.inl 3, 7042968904082227200000), (Sum.inl 4, 2347656301360742400000), (Sum.inl 12, 4695312602721484800000), (Sum.inl 13, 2347656301360742400000)]

def reducedTerm369 : Integer.Sparse Master := [(Sum.inl 0, 226022418999982080000), (Sum.inl 1, 627840052777728000000), (Sum.inl 2, 251136021111091200000), (Sum.inl 3, 2009088168888729600000), (Sum.inl 13, 2009088168888729600000)]

def reducedTerm370 : Integer.Sparse Master := []

def reducedTerm371 : Integer.Sparse Master := [(Sum.inl 0, -29819547878400000000), (Sum.inl 1, -111823304544000000000), (Sum.inl 2, 53249192640000000000), (Sum.inl 3, 766788374016000000000), (Sum.inl 4, 255596124672000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 12, 340794832896000000000), (Sum.inl 26, 170397416448000000000), (Sum.inl 27, -63899031168000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 195, 511192249344000000000)]

def reducedTerm372 : Integer.Sparse Master := [(Sum.inl 0, -196903076374609920000), (Sum.inl 1, -1007411088428236800000), (Sum.inl 2, -91582826220748800000), (Sum.inl 3, 1465325219531980800000), (Sum.inl 5, 91582826220748800000), (Sum.inl 6, -22895706555187200000), (Sum.inl 7, 732662609765990400000), (Sum.inl 12, 732662609765990400000), (Sum.inl 23, -1098993914648985600000), (Sum.inl 27, -274748478662246400000)]

def reducedTerm373 : Integer.Sparse Master := [(Sum.inl 0, 53298369661501440000), (Sum.inl 1, -23173204200652800000), (Sum.inl 2, -52139709451468800000), (Sum.inl 3, -278078450407833600000), (Sum.inl 4, -185385633605222400000), (Sum.inl 5, -23173204200652800000), (Sum.inl 6, 5793301050163200000), (Sum.inl 7, -92692816802611200000), (Sum.inl 8, -92692816802611200000), (Sum.inl 24, 278078450407833600000), (Sum.inl 27, 69519612601958400000)]

def reducedTerm374 : Integer.Sparse Master := [(Sum.inl 0, -225099889665638400000), (Sum.inl 1, 281374862082048000000), (Sum.inl 2, -35171857760256000000), (Sum.inl 3, 2250998896656384000000), (Sum.inl 4, 1125499448328192000000), (Sum.inl 5, 281374862082048000000), (Sum.inl 6, -35171857760256000000), (Sum.inl 25, -3376498344984576000000), (Sum.inl 26, 1125499448328192000000), (Sum.inl 27, -422062293123072000000), (Sum.inl 31, -1688249172492288000000), (Sum.inl 33, -3376498344984576000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3376498344984576000000), (Sum.inl 123, -1688249172492288000000)]

def reducedTerm375 : Integer.Sparse Master := [(Sum.inl 0, -26624596320000000000), (Sum.inl 1, -138447900864000000000), (Sum.inl 2, 21299677056000000000), (Sum.inl 3, 596390957568000000000), (Sum.inl 4, 255596124672000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 12, 255596124672000000000), (Sum.inl 25, -511192249344000000000), (Sum.inl 26, 85198708224000000000), (Sum.inl 27, -63899031168000000000), (Sum.inl 31, -511192249344000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 55, -255596124672000000000), (Sum.inl 64, -255596124672000000000), (Sum.inl 123, -255596124672000000000)]

def reducedTerm376 : Integer.Sparse Master := [(Sum.inl 0, 134703801579110400000), (Sum.inl 2, 259045772267520000000), (Sum.inl 3, -1657892942512128000000), (Sum.inl 4, -828946471256064000000), (Sum.inl 25, 1243419706884096000000), (Sum.inl 26, -828946471256064000000)]

def reducedTerm377 : Integer.Sparse Master := [(Sum.inl 0, 560396443299840000), (Sum.inl 1, 3402406977177600000), (Sum.inl 2, -1000707934464000000), (Sum.inl 3, -16011326951424000000), (Sum.inl 4, -6404530780569600000), (Sum.inl 12, -6404530780569600000), (Sum.inl 26, -3202265390284800000)]

def reducedTerm378 : Integer.Sparse Master := [(Sum.inl 0, -117262652500224000000), (Sum.inl 1, -703575915001344000000), (Sum.inl 2, 273612855833856000000), (Sum.inl 3, 5003206506676224000000), (Sum.inl 4, 1250801626669056000000), (Sum.inl 12, 2501603253338112000000), (Sum.inl 13, 2501603253338112000000), (Sum.inl 26, 625400813334528000000), (Sum.inl 33, -3752404880007168000000), (Sum.inl 34, 625400813334528000000)]

def reducedTerm379 : Integer.Sparse Master := [(Sum.inl 0, -102521110594129920000), (Sum.inl 1, -419404543339622400000), (Sum.inl 3, 4473648462289305600000), (Sum.inl 12, 2236824231144652800000), (Sum.inl 13, 4473648462289305600000), (Sum.inl 34, 745608077048217600000)]

def reducedTerm380 : Integer.Sparse Master := []

def reducedTerm381 : Integer.Sparse Master := [(Sum.inl 0, -415170565808947200000), (Sum.inl 1, 908185612707072000000), (Sum.inl 2, -648704009076480000000), (Sum.inl 3, -2075852829044736000000), (Sum.inl 12, -1037926414522368000000)]

def reducedTerm382 : Integer.Sparse Master := [(Sum.inl 0, -1870131632947200000), (Sum.inl 1, -93506581647360000000), (Sum.inl 2, 46753290823680000000), (Sum.inl 3, 523636857225216000000), (Sum.inl 4, 299221061271552000000), (Sum.inl 12, 149610530635776000000), (Sum.inl 25, -448831591907328000000), (Sum.inl 26, 74805265317888000000), (Sum.inl 31, -448831591907328000000), (Sum.inl 33, -673247387860992000000)]

def reducedTerm383 : Integer.Sparse Master := [(Sum.inl 0, 8519870822400000000), (Sum.inl 1, 212996770560000000000), (Sum.inl 2, -85198708224000000000), (Sum.inl 3, -1192781915136000000000), (Sum.inl 4, -511192249344000000000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 511192249344000000000), (Sum.inl 26, -511192249344000000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, 511192249344000000000), (Sum.inl 34, -170397416448000000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm384 : Integer.Sparse Master := [(Sum.inl 0, -2000049669273600000), (Sum.inl 1, 560013907396608000000), (Sum.inl 2, -90002235117312000000), (Sum.inl 3, -1440035761876992000000), (Sum.inl 4, -960023841251328000000), (Sum.inl 12, -640015894167552000000), (Sum.inl 25, 480011920625664000000), (Sum.inl 26, -320007947083776000000)]

def reducedTerm385 : Integer.Sparse Master := [(Sum.inl 0, 573273375381504000000), (Sum.inl 1, -1194319532044800000000), (Sum.inl 2, 716591719226880000000), (Sum.inl 3, 3821822502543360000000), (Sum.inl 4, 1910911251271680000000), (Sum.inl 25, -5732733753815040000000), (Sum.inl 26, 1910911251271680000000)]

def reducedTerm386 : Integer.Sparse Master := [(Sum.inl 0, -33601146090946560000), (Sum.inl 1, -104279418902937600000), (Sum.inl 2, 52139709451468800000), (Sum.inl 3, 278078450407833600000), (Sum.inl 4, 185385633605222400000), (Sum.inl 12, 185385633605222400000)]

def reducedTerm387 : Integer.Sparse Master := [(Sum.inl 0, 6528512419430400000), (Sum.inl 1, -4760373639168000000), (Sum.inl 2, 3400266885120000000), (Sum.inl 3, 10880854032384000000), (Sum.inl 4, 10880854032384000000)]

def reducedTerm388 : Integer.Sparse Master := [(Sum.inl 0, -223214231274209280000), (Sum.inl 1, 992063250107596800000), (Sum.inl 2, -124007906263449600000), (Sum.inl 3, -992063250107596800000), (Sum.inl 12, -992063250107596800000)]

def reducedTerm389 : Integer.Sparse Master := [(Sum.inl 0, 428378320014704640000), (Sum.inl 1, -2409628050082713600000), (Sum.inl 2, 803209350027571200000), (Sum.inl 3, 4283783200147046400000), (Sum.inl 12, 4283783200147046400000), (Sum.inl 33, -12851349600441139200000)]

def reducedTerm390 : Integer.Sparse Master := [(Sum.inl 0, -88922745354240000), (Sum.inl 1, -5335364721254400000), (Sum.inl 2, 1333841180313600000), (Sum.inl 3, 21341458885017600000), (Sum.inl 13, 14227639256678400000)]

def reducedTerm391 : Integer.Sparse Master := [(Sum.inl 0, 219538591211520000000), (Sum.inl 1, -823269717043200000000), (Sum.inl 2, 54884647802880000000), (Sum.inl 3, 2634463094538240000000), (Sum.inl 4, 1756308729692160000000), (Sum.inl 12, 878154364846080000000), (Sum.inl 26, 878154364846080000000)]

def reducedTerm392 : Integer.Sparse Master := [(Sum.inl 0, 149201132044124160000), (Sum.inl 1, 859036820860108800000), (Sum.inl 2, -22606232127897600000), (Sum.inl 3, 361699714046361600000), (Sum.inl 12, 361699714046361600000)]

def reducedTerm393 : Integer.Sparse Master := []

def reducedTerm394 : Integer.Sparse Master := [(Sum.inl 0, -559206427749580800000), (Sum.inl 1, -1864021425831936000000), (Sum.inl 2, -186402142583193600000), (Sum.inl 3, 2982434281331097600000), (Sum.inl 12, 2982434281331097600000)]

def reducedTerm395 : Integer.Sparse Master := [(Sum.inl 1, 244946286144000000000), (Sum.inl 2, -53249192640000000000), (Sum.inl 3, -681589665792000000000), (Sum.inl 4, -340794832896000000000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 511192249344000000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, 511192249344000000000)]

def reducedTerm396 : Integer.Sparse Master := [(Sum.inl 0, 66696097521715200000), (Sum.inl 1, -151582039822080000000), (Sum.inl 2, 60632815928832000000), (Sum.inl 3, 485062527430656000000), (Sum.inl 4, 485062527430656000000), (Sum.inl 25, -1455187582291968000000), (Sum.inl 31, -1455187582291968000000), (Sum.inl 33, -1455187582291968000000)]

def reducedTerm397 : Integer.Sparse Master := [(Sum.inl 0, -34000844377651200000), (Sum.inl 1, 720017880938496000000), (Sum.inl 2, -90002235117312000000), (Sum.inl 3, -1440035761876992000000), (Sum.inl 4, -960023841251328000000), (Sum.inl 12, -960023841251328000000), (Sum.inl 13, -320007947083776000000)]

def reducedTerm398 : Integer.Sparse Master := [(Sum.inl 0, -8000198677094400000), (Sum.inl 1, -100002483463680000000), (Sum.inl 2, 20000496692736000000), (Sum.inl 3, -160003973541888000000), (Sum.inl 12, -160003973541888000000), (Sum.inl 25, 240005960312832000000)]

def reducedTerm399 : Integer.Sparse Master := [(Sum.inl 0, 63766106482176000000), (Sum.inl 1, 255064425928704000000), (Sum.inl 2, 63766106482176000000), (Sum.inl 25, 1530386555572224000000)]

def reducedTerm400 : Integer.Sparse Master := [(Sum.inl 0, -12074021169315840000), (Sum.inl 1, 35511826968576000000), (Sum.inl 2, 3551182696857600000), (Sum.inl 3, -56818923149721600000), (Sum.inl 4, -56818923149721600000), (Sum.inl 12, -28409461574860800000)]

def reducedTerm401 : Integer.Sparse Master := [(Sum.inl 0, -1125418994453053440000), (Sum.inl 1, 1563081936740352000000), (Sum.inl 2, -312616387348070400000), (Sum.inl 3, 5001862197569126400000), (Sum.inl 4, 5001862197569126400000)]

def reducedTerm402 : Integer.Sparse Master := [(Sum.inl 0, 59076484862976000000), (Sum.inl 1, -126592467563520000000), (Sum.inl 12, 67515982700544000000)]

def reducedTerm403 : Integer.Sparse Master := [(Sum.inl 0, -63754825907404800000), (Sum.inl 1, -191264477722214400000), (Sum.inl 12, 255019303629619200000)]

def reducedTerm404 : Integer.Sparse Master := []

def reducedTerm405 : Integer.Sparse Master := [(Sum.inl 0, -85217042524078080000), (Sum.inl 1, -1278255637861171200000), (Sum.inl 12, -1704340850481561600000)]

def reducedTerm406 : Integer.Sparse Master := [(Sum.inl 0, -139774235915059200000), (Sum.inl 1, -53759321505792000000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 24, -645111858069504000000), (Sum.inl 27, -483833893552128000000), (Sum.inl 30, -1290223716139008000000)]

def reducedTerm407 : Integer.Sparse Master := [(Sum.inl 0, 516089486455603200000), (Sum.inl 1, 322555929034752000000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 27, -483833893552128000000), (Sum.inl 30, -1935335574208512000000)]

def reducedTerm408 : Integer.Sparse Master := [(Sum.inl 0, -139774235915059200000), (Sum.inl 1, -53759321505792000000), (Sum.inl 27, -322555929034752000000), (Sum.inl 30, -1290223716139008000000)]

def reducedTerm409 : Integer.Sparse Master := []

def reducedTerm410 : Integer.Sparse Master := [(Sum.inl 1, 320007947083776000000), (Sum.inl 2, -80001986770944000000), (Sum.inl 3, -320007947083776000000), (Sum.inl 4, -320007947083776000000), (Sum.inl 12, -80001986770944000000), (Sum.inl 31, 480011920625664000000)]

def reducedTerm411 : Integer.Sparse Master := [(Sum.inl 0, -93814003219507200000), (Sum.inl 1, 60525163367424000000), (Sum.inl 2, -45393872525568000000), (Sum.inl 3, -242100653469696000000), (Sum.inl 4, -242100653469696000000), (Sum.inl 31, 726301960409088000000)]

def reducedTerm412 : Integer.Sparse Master := []

def reducedTerm413 : Integer.Sparse Master := [(Sum.inl 0, -47501771756544000000), (Sum.inl 1, 41913328020480000000), (Sum.inl 2, -27942218680320000000), (Sum.inl 31, -670613248327680000000)]

def reducedTerm414 : Integer.Sparse Master := [(Sum.inl 0, -137086269839769600000), (Sum.inl 1, -268796607528960000000), (Sum.inl 2, 161277964517376000000), (Sum.inl 5, 53759321505792000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 430074572046336000000), (Sum.inl 27, -161277964517376000000), (Sum.inl 30, -645111858069504000000)]

def reducedTerm415 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm416 : Integer.Sparse Master := [(Sum.inl 0, 358405884591390720000), (Sum.inl 1, 1753901137362124800000), (Sum.inl 2, -419411141543116800000), (Sum.inl 3, -610052569517260800000), (Sum.inl 4, -1220105139034521600000)]

def reducedTerm417 : Integer.Sparse Master := [(Sum.inl 0, -429052445894983680000), (Sum.inl 1, 390047678086348800000), (Sum.inl 2, -195023839043174400000)]

def reducedTerm419 : Integer.Sparse Master := [(Sum.inl 0, -486085768070676480000), (Sum.inl 1, 544125859780608000000), (Sum.inl 4, -580400917099315200000)]

def reducedTerm420 : Integer.Sparse Master := [(Sum.inl 0, 183015770855178240000), (Sum.inl 1, 915078854275891200000)]

def reducedTerm421 : Integer.Sparse Master := [(Sum.inl 0, 2333634343649280000), (Sum.inl 1, -1521935441510400000), (Sum.inl 4, -8116989021388800000)]

def reducedTerm422 : Integer.Sparse Master := []

def reducedTerm423 : Integer.Sparse Master := [(Sum.inl 0, 196910301321216000000), (Sum.inl 1, -421950645688320000000), (Sum.inl 4, 2250403443671040000000)]

def reducedTerm424 : Integer.Sparse Master := [(Sum.inl 0, 1204186356864368640000), (Sum.inl 1, 1600500854060236800000), (Sum.inl 12, -609714611070566400000)]

def reducedTerm425 : Integer.Sparse Master := []

def reducedTerm426 : Integer.Sparse Master := [(Sum.inl 0, -105737073514168320000), (Sum.inl 1, -236221121680588800000), (Sum.inl 4, 179977997470924800000)]

def reducedTerm427 : Integer.Sparse Master := [(Sum.inr 577, -654308882759024640000)]

def reducedTerm428 : Integer.Sparse Master := [(Sum.inr 578, -2282493232765992960000)]

def reducedTerm429 : Integer.Sparse Master := [(Sum.inr 579, 654308882759024640000)]

def reducedTerm430 : Integer.Sparse Master := [(Sum.inr 580, 877592856526848000000)]

def reducedTerm431 : Integer.Sparse Master := [(Sum.inr 581, 877447660307742720000)]

def reducedTerm432 : Integer.Sparse Master := [(Sum.inr 582, 607591276892651520000)]

def reducedTerm433 : Integer.Sparse Master := [(Sum.inr 583, 2282493232765992960000)]

def reducedTerm434 : Integer.Sparse Master := [(Sum.inr 584, -113253321790586880000)]

def reducedTerm435 : Integer.Sparse Master := [(Sum.inr 585, -2325444766551244800000)]

def reducedTerm436 : Integer.Sparse Master := [(Sum.inr 586, -878028445184163840000)]

def reducedTerm437 : Integer.Sparse Master := [(Sum.inr 587, 4950070676784414720000)]

def reducedTerm438 : Integer.Sparse Master := [(Sum.inr 588, -947351242264412160000)]

def reducedTerm439 : Integer.Sparse Master := [(Sum.inr 589, -877883248965058560000)]

def reducedTerm440 : Integer.Sparse Master := [(Sum.inr 590, -544816666760970240000)]

def reducedTerm441 : Integer.Sparse Master := [(Sum.inr 591, 2291676713032089600000)]

def reducedTerm442 : Integer.Sparse Master := [(Sum.inr 597, -28541892592926720000)]

def reducedTerm443 : Integer.Sparse Master := [(Sum.inr 599, -1211529171307069440000)]

def reducedTerm444 : Integer.Sparse Master := [(Sum.inr 600, 344588552322416640000)]

def reducedTerm445 : Integer.Sparse Master := [(Sum.inr 601, 28541892592926720000)]

def reducedTerm446 : Integer.Sparse Master := [(Sum.inr 603, 533546803510640640000)]

def reducedTerm447 : Integer.Sparse Master := [(Sum.inr 604, 6690208535414046720000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm448 : Integer.Sparse Master := [(Sum.inr 605, -2453660793490636800000)]

def reducedTerm449 : Integer.Sparse Master := [(Sum.inr 606, 1441480432653434880000)]

def reducedTerm450 : Integer.Sparse Master := [(Sum.inr 607, 2300979745408942080000)]

def reducedTerm451 : Integer.Sparse Master := [(Sum.inr 608, -1054181617875025920000)]

def reducedTerm452 : Integer.Sparse Master := [(Sum.inr 610, -9473152863350292480000)]

def reducedTerm453 : Integer.Sparse Master := [(Sum.inr 611, 18388973290326589440000)]

def reducedTerm454 : Integer.Sparse Master := [(Sum.inr 612, -584459388199895040000)]

def reducedTerm455 : Integer.Sparse Master := [(Sum.inr 613, -2602745435968634880000)]

def reducedTerm456 : Integer.Sparse Master := [(Sum.inr 614, 677982367796428800000)]

def reducedTerm457 : Integer.Sparse Master := [(Sum.inr 615, 1801435404238848000000)]

def reducedTerm458 : Integer.Sparse Master := [(Sum.inr 616, -2365767237453742080000)]

def reducedTerm459 : Integer.Sparse Master := [(Sum.inr 617, 3002873618910412800000)]

def reducedTerm460 : Integer.Sparse Master := [(Sum.inr 618, 1287214867623444480000)]

def reducedTerm461 : Integer.Sparse Master := [(Sum.inr 619, 3163253859043246080000)]

def reducedTerm462 : Integer.Sparse Master := [(Sum.inr 620, 9267211259630714880000)]

def reducedTerm463 : Integer.Sparse Master := [(Sum.inr 621, 365728146625658880000)]

def reducedTerm464 : Integer.Sparse Master := [(Sum.inr 622, -820112129438515200000)]

def reducedTerm465 : Integer.Sparse Master := [(Sum.inr 623, -1258494730418257920000)]

def reducedTerm466 : Integer.Sparse Master := [(Sum.inr 624, -363229471392399360000)]

def reducedTerm467 : Integer.Sparse Master := [(Sum.inr 626, 4002258833827430400000)]

def reducedTerm468 : Integer.Sparse Master := [(Sum.inr 627, -860150167449108480000)]

def reducedTerm469 : Integer.Sparse Master := [(Sum.inr 628, 363229471392399360000)]

def reducedTerm470 : Integer.Sparse Master := [(Sum.inr 629, 1355923199361024000000)]

def reducedTerm471 : Integer.Sparse Master := [(Sum.inr 630, -1355923199361024000000)]

def reducedTerm472 : Integer.Sparse Master := [(Sum.inr 631, -3620046943302451200000)]

def reducedTerm473 : Integer.Sparse Master := [(Sum.inr 633, 4614435349529886720000)]

def reducedTerm474 : Integer.Sparse Master := [(Sum.inr 634, -4581648092858941440000)]

def reducedTerm475 : Integer.Sparse Master := [(Sum.inr 635, -1883613935960064000000)]

def reducedTerm476 : Integer.Sparse Master := [(Sum.inr 636, -3999431119401123840000)]

def reducedTerm477 : Integer.Sparse Master := [(Sum.inr 637, 5023829814312960000000)]

def reducedTerm478 : Integer.Sparse Master := [(Sum.inr 638, 5237719375993896960000)]

def reducedTerm479 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm480 : Integer.Sparse Master := [(Sum.inr 640, -5023829814312960000000)]

def reducedTerm481 : Integer.Sparse Master := [(Sum.inr 641, 2600840819146752000000)]

def reducedTerm482 : Integer.Sparse Master := [(Sum.inr 642, -7838560195140648960000)]

def reducedTerm483 : Integer.Sparse Master := [(Sum.inr 643, 3501219910680576000000)]

def reducedTerm484 : Integer.Sparse Master := [(Sum.inr 653, 892167378500321280000)]

def reducedTerm485 : Integer.Sparse Master := [(Sum.inr 654, 315973519843000320000)]

def reducedTerm486 : Integer.Sparse Master := [(Sum.inr 909, 8659257895151861760000)]

def reducedTerm487 : Integer.Sparse Master := [(Sum.inr 911, 7407336363717427200000)]

def reducedTerm488 : Integer.Sparse Master := [(Sum.inr 914, 8137792988223897600000)]

def reducedTerm489 : Integer.Sparse Master := [(Sum.inr 922, 842806262366208000000)]

def reducedTerm490 : Integer.Sparse Master := [(Sum.inr 929, -941481721225543680000)]

def reducedTerm491 : Integer.Sparse Master := [(Sum.inr 930, -4522163694065418240000)]

def reducedTerm492 : Integer.Sparse Master := [(Sum.inr 931, 862331180804997120000)]

def reducedTerm493 : Integer.Sparse Master := [(Sum.inr 932, -2281209943794647040000)]

def reducedTerm494 : Integer.Sparse Master := [(Sum.inr 933, -842806262366208000000)]

def reducedTerm495 : Integer.Sparse Master := [(Sum.inr 934, 1048155974782156800000)]

def reducedTerm496 : Integer.Sparse Master := [(Sum.inr 936, -3501622812129361920000)]

def reducedTerm497 : Integer.Sparse Master := [(Sum.inr 937, -690110044530278400000)]

def reducedTerm498 : Integer.Sparse Master := [(Sum.inr 939, -5644648033344552960000)]

def reducedTerm499 : Integer.Sparse Master := [(Sum.inr 940, -3110224913045913600000)]

def reducedTerm500 : Integer.Sparse Master := [(Sum.inr 944, 5755499567677440000000)]

def reducedTerm501 : Integer.Sparse Master := [(Sum.inr 945, 5755499567677440000000)]

def reducedTerm502 : Integer.Sparse Master := [(Sum.inr 946, 4959624732475392000000)]

def reducedTerm503 : Integer.Sparse Master := [(Sum.inr 949, -7458564352880148480000)]

def reducedTerm504 : Integer.Sparse Master := [(Sum.inr 950, -5755499567677440000000)]

def reducedTerm505 : Integer.Sparse Master := [(Sum.inr 951, 7458564352880148480000)]

def reducedTerm506 : Integer.Sparse Master := [(Sum.inr 952, -4959624732475392000000)]

def reducedTerm507 : Integer.Sparse Master := [(Sum.inr 953, -5755499567677440000000)]

def reducedTerm508 : Integer.Sparse Master := [(Sum.inr 954, -3501219910680576000000)]

def reducedTerm509 : Integer.Sparse Master := [(Sum.inr 1024, -2976678613712240640000)]

def reducedTerm510 : Integer.Sparse Master := [(Sum.inr 1027, -4206296272205905920000)]

def reducedTerm511 : Integer.Sparse Master := [(Sum.inr 1039, 84218592777338880000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm512 : Integer.Sparse Master := [(Sum.inr 1041, -1011243447920885760000)]

def reducedTerm513 : Integer.Sparse Master := [(Sum.inr 1044, -2007773678972436480000)]

def reducedTerm514 : Integer.Sparse Master := [(Sum.inr 1046, 10725266364412723200000)]

def reducedTerm515 : Integer.Sparse Master := [(Sum.inr 1047, -13781464017158799360000)]

def reducedTerm516 : Integer.Sparse Master := [(Sum.inr 1049, 1567784528782295040000)]

def reducedTerm517 : Integer.Sparse Master := [(Sum.inr 1050, 927024855143546880000)]

def reducedTerm518 : Integer.Sparse Master := [(Sum.inr 1051, 1191593947134689280000)]

def reducedTerm519 : Integer.Sparse Master := [(Sum.inr 1058, 6300739362226176000000)]

def reducedTerm520 : Integer.Sparse Master := [(Sum.inr 1061, -3750701327642787840000)]

def reducedTerm521 : Integer.Sparse Master := [(Sum.inr 1063, -6300739362226176000000)]

def reducedTerm522 : Integer.Sparse Master := [(Sum.inr 1064, 3750701327642787840000)]

def reducedTerm523 : Integer.Sparse Master := [(Sum.inr 1087, -8631272678361661440000)]

def reducedTerm524 : Integer.Sparse Master := [(Sum.inr 1091, 7331333818189086720000)]

def reducedTerm525 : Integer.Sparse Master := [(Sum.inr 1094, -2107338916154572800000)]

def reducedTerm526 : Integer.Sparse Master := [(Sum.inr 1111, 94866766992506880000)]

def reducedTerm527 : Integer.Sparse Master := [(Sum.inr 1112, -26389657073487052800000)]

def reducedTerm528 : Integer.Sparse Master := [(Sum.inr 1113, -8810814575497052160000)]

def reducedTerm529 : Integer.Sparse Master := [(Sum.inr 1115, -1573216023167631360000)]

def reducedTerm530 : Integer.Sparse Master := [(Sum.inr 1116, -1126879414384066560000)]

def reducedTerm531 : Integer.Sparse Master := [(Sum.inr 1117, -250586732209766400000)]

def reducedTerm532 : Integer.Sparse Master := [(Sum.inr 1118, 4772950974038016000000)]

def reducedTerm533 : Integer.Sparse Master := [(Sum.inr 1119, -1307377367220879360000)]

def reducedTerm534 : Integer.Sparse Master := [(Sum.inr 1120, 6812136157446144000000)]

def reducedTerm535 : Integer.Sparse Master := [(Sum.inr 1121, -8762782347893145600000)]

def reducedTerm536 : Integer.Sparse Master := [(Sum.inr 1125, 416003421044736000000)]

def reducedTerm537 : Integer.Sparse Master := [(Sum.inr 1126, 3128439995443445760000)]

def reducedTerm538 : Integer.Sparse Master := [(Sum.inr 1128, 331078441437757440000)]

def reducedTerm539 : Integer.Sparse Master := [(Sum.inr 1129, 19378969510926090240000)]

def reducedTerm540 : Integer.Sparse Master := [(Sum.inr 1130, -9464678117613895680000)]

def reducedTerm541 : Integer.Sparse Master := [(Sum.inr 1131, 5641023726228602880000)]

def reducedTerm542 : Integer.Sparse Master := [(Sum.inr 1132, -1759585423361310720000)]

def reducedTerm543 : Integer.Sparse Master := [(Sum.inr 1133, 1307514346489774080000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm544 : Integer.Sparse Master := [(Sum.inr 1134, 3771399734927032320000)]

def reducedTerm545 : Integer.Sparse Master := [(Sum.inr 1135, -4459227814998835200000)]

def reducedTerm546 : Integer.Sparse Master := [(Sum.inr 1137, 467378502645841920000)]

def reducedTerm547 : Integer.Sparse Master := [(Sum.inr 1138, -19215558570607902720000)]

def reducedTerm548 : Integer.Sparse Master := [(Sum.inr 1139, -10083993537718517760000)]

def reducedTerm549 : Integer.Sparse Master := [(Sum.inr 1140, 5594674980160143360000)]

def reducedTerm550 : Integer.Sparse Master := [(Sum.inr 1141, 871459791106867200000)]

def reducedTerm551 : Integer.Sparse Master := [(Sum.inr 1142, 5137435020224102400000)]

def reducedTerm552 : Integer.Sparse Master := [(Sum.inr 1143, -5549518414241464320000)]

def reducedTerm553 : Integer.Sparse Master := [(Sum.inr 1144, -2210692257679933440000)]

def reducedTerm554 : Integer.Sparse Master := [(Sum.inr 1145, 2991047260449669120000)]

def reducedTerm555 : Integer.Sparse Master := [(Sum.inr 1146, 167779287760896000000)]

def reducedTerm556 : Integer.Sparse Master := [(Sum.inr 1148, -54778388874854400000)]

def reducedTerm557 : Integer.Sparse Master := [(Sum.inr 1149, 54778388874854400000)]

def reducedTerm558 : Integer.Sparse Master := [(Sum.inr 1150, 598839592845312000000)]

def reducedTerm559 : Integer.Sparse Master := [(Sum.inr 1151, -3796503149893386240000)]

def reducedTerm560 : Integer.Sparse Master := [(Sum.inr 1153, -2713512723987824640000)]

def reducedTerm561 : Integer.Sparse Master := [(Sum.inr 1155, 3773107777016954880000)]

def reducedTerm562 : Integer.Sparse Master := [(Sum.inr 1156, -4033883256599347200000)]

def reducedTerm563 : Integer.Sparse Master := [(Sum.inr 1159, -1465158899028787200000)]

def reducedTerm564 : Integer.Sparse Master := [(Sum.inr 1160, 5499042155628134400000)]

def reducedTerm565 : Integer.Sparse Master := [(Sum.inr 1169, 4433171053215744000000)]

def reducedTerm566 : Integer.Sparse Master := [(Sum.inr 1171, 6851070957020774400000)]

def reducedTerm567 : Integer.Sparse Master := [(Sum.inr 1174, 606438917347737600000)]

def reducedTerm568 : Integer.Sparse Master := [(Sum.inr 1212, 934778270036459520000)]

def reducedTerm569 : Integer.Sparse Master := [(Sum.inr 1215, -1029645037028966400000)]

def reducedTerm570 : Integer.Sparse Master := [(Sum.inr 1216, 250586732209766400000)]

def reducedTerm571 : Integer.Sparse Master := [(Sum.inr 1217, 18978681323195596800000)]

def reducedTerm572 : Integer.Sparse Master := [(Sum.inr 1219, 11351689807634104320000)]

def reducedTerm573 : Integer.Sparse Master := [(Sum.inr 1221, 972527074748006400000)]

def reducedTerm574 : Integer.Sparse Master := [(Sum.inr 1233, -6722247552986972160000)]

def reducedTerm575 : Integer.Sparse Master := [(Sum.inr 1234, -416003421044736000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm576 : Integer.Sparse Master := [(Sum.inr 1235, 3252202435368714240000)]

def reducedTerm577 : Integer.Sparse Master := [(Sum.inr 1236, 12119156027369717760000)]

def reducedTerm578 : Integer.Sparse Master := [(Sum.inr 1237, 6722247552986972160000)]

def reducedTerm579 : Integer.Sparse Master := [(Sum.inr 1239, -2570828363354603520000)]

def reducedTerm580 : Integer.Sparse Master := [(Sum.inr 1240, -12547178408576286720000)]

def reducedTerm581 : Integer.Sparse Master := [(Sum.inr 1241, 8753467817805742080000)]

def reducedTerm582 : Integer.Sparse Master := [(Sum.inr 1242, -3100873301337047040000)]

def reducedTerm583 : Integer.Sparse Master := [(Sum.inr 1243, -2614211302075269120000)]

def reducedTerm584 : Integer.Sparse Master := [(Sum.inr 1245, 7725885129934110720000)]

def reducedTerm585 : Integer.Sparse Master := [(Sum.inr 1246, -19348453924951818240000)]

def reducedTerm586 : Integer.Sparse Master := [(Sum.inr 1260, -7062722889655910400000)]

def reducedTerm587 : Integer.Sparse Master := [(Sum.inr 1261, -9103216750304624640000)]

def reducedTerm588 : Integer.Sparse Master := [(Sum.inr 1262, 7062722889655910400000)]

def reducedTerm589 : Integer.Sparse Master := [(Sum.inr 1264, 8502527801884999680000)]

def reducedTerm590 : Integer.Sparse Master := [(Sum.inr 1270, -8079242612869693440000)]

def reducedTerm591 : Integer.Sparse Master := [(Sum.inr 1273, -5076859302087229440000)]

def reducedTerm592 : Integer.Sparse Master := [(Sum.inr 1291, -2206050538624450560000)]

def reducedTerm593 : Integer.Sparse Master := [(Sum.inr 1292, 2219882239269273600000)]

def reducedTerm594 : Integer.Sparse Master := [(Sum.inr 1293, 4459227814998835200000)]

def reducedTerm595 : Integer.Sparse Master := [(Sum.inr 1294, 11729049453615513600000)]

def reducedTerm596 : Integer.Sparse Master := [(Sum.inr 1295, 2206050538624450560000)]

def reducedTerm597 : Integer.Sparse Master := [(Sum.inr 1297, 5575466278860226560000)]

def reducedTerm598 : Integer.Sparse Master := [(Sum.inr 1306, -6047328798324817920000)]

def reducedTerm599 : Integer.Sparse Master := [(Sum.inr 1310, -626180907745935360000)]

def reducedTerm600 : Integer.Sparse Master := [(Sum.inr 1314, 5977466481711513600000)]

def reducedTerm601 : Integer.Sparse Master := [(Sum.inr 1315, 3501622812129361920000)]

def reducedTerm602 : Integer.Sparse Master := [(Sum.inr 1316, -9579839035999518720000)]

def reducedTerm603 : Integer.Sparse Master := [(Sum.inr 1317, 7341542882196848640000)]

def reducedTerm604 : Integer.Sparse Master := [(Sum.inr 1318, -4432587559454638080000)]

def reducedTerm605 : Integer.Sparse Master := [(Sum.inr 1319, -3032742142629642240000)]

def reducedTerm606 : Integer.Sparse Master := [(Sum.inr 1320, 11886766950399344640000)]

def reducedTerm607 : Integer.Sparse Master := [(Sum.inr 1321, -10548491592982855680000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm608 : Integer.Sparse Master := [(Sum.inr 1322, 9579839035999518720000)]

def reducedTerm609 : Integer.Sparse Master := [(Sum.inr 1323, -4933072605979607040000)]

def reducedTerm610 : Integer.Sparse Master := [(Sum.inr 1324, -8886421804453724160000)]

def reducedTerm611 : Integer.Sparse Master := [(Sum.inr 1325, -8635312347795947520000)]

def reducedTerm612 : Integer.Sparse Master := [(Sum.inr 1326, 277114839928012800000)]

def reducedTerm613 : Integer.Sparse Master := [(Sum.inr 1327, -5341116330562682880000)]

def reducedTerm614 : Integer.Sparse Master := [(Sum.inr 1328, -2299907207666073600000)]

def reducedTerm615 : Integer.Sparse Master := [(Sum.inr 1330, -819339736118722560000)]

def reducedTerm616 : Integer.Sparse Master := [(Sum.inr 1332, -3493413807980544000000)]

def reducedTerm617 : Integer.Sparse Master := [(Sum.inr 1333, 7641023538228756480000)]

def reducedTerm618 : Integer.Sparse Master := [(Sum.inr 1334, 8698253102854963200000)]

def reducedTerm619 : Integer.Sparse Master := [(Sum.inr 1335, 7361272231133184000000)]

def reducedTerm620 : Integer.Sparse Master := [(Sum.inr 1336, 3435031202884485120000)]

def reducedTerm621 : Integer.Sparse Master := [(Sum.inr 1337, -1895122181062656000000)]

def reducedTerm622 : Integer.Sparse Master := [(Sum.inr 1338, 4158977745420288000000)]

def reducedTerm623 : Integer.Sparse Master := [(Sum.inr 1348, 1542086242739159040000)]

def reducedTerm624 : Integer.Sparse Master := [(Sum.inr 1366, -1899117244195799040000)]

def reducedTerm625 : Integer.Sparse Master := [(Sum.inr 1367, 2667259420956426240000)]

def reducedTerm626 : Integer.Sparse Master := [(Sum.inr 1369, -3750701327642787840000)]

def reducedTerm627 : Integer.Sparse Master := [(Sum.inr 1370, 1899117244195799040000)]

def reducedTerm628 : Integer.Sparse Master := [(Sum.inr 1372, 8859486641663508480000)]

def reducedTerm629 : Integer.Sparse Master := [(Sum.inr 1375, -11526746062619934720000)]

def reducedTerm630 : Integer.Sparse Master := [(Sum.inr 1383, 4656026210537963520000)]

def reducedTerm631 : Integer.Sparse Master := [(Sum.inr 1385, -3478154931439534080000)]

def reducedTerm632 : Integer.Sparse Master := [(Sum.inr 1388, -2299907207666073600000)]

def reducedTerm633 : Integer.Sparse Master := [(Sum.inr 1391, -2356119002871889920000)]

def reducedTerm634 : Integer.Sparse Master := [(Sum.inr 1406, -22276992136265072640000)]

def reducedTerm635 : Integer.Sparse Master := [(Sum.inr 1408, -17269758213677383680000)]

def reducedTerm636 : Integer.Sparse Master := [(Sum.inr 1435, 847409560407244800000)]

def reducedTerm637 : Integer.Sparse Master := [(Sum.inr 1436, -3245969833485926400000)]

def reducedTerm638 : Integer.Sparse Master := [(Sum.inr 1438, 39708998817546240000)]

def reducedTerm639 : Integer.Sparse Master := [(Sum.inr 1501, -1056230257065984000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm64 : Integer.Sparse Master := [(Sum.inl 0, 166157862258769920000), (Sum.inl 1, 92309923477094400000), (Sum.inl 5, 923099234770944000000), (Sum.inl 8, -738479387816755200000)]

def reducedTerm65 : Integer.Sparse Master := [(Sum.inl 0, -6100282898841600000), (Sum.inl 1, 12200565797683200000), (Sum.inl 5, 24401131595366400000), (Sum.inl 6, -30501414494208000000)]

def reducedTerm66 : Integer.Sparse Master := [(Sum.inl 0, -24575771049984000000), (Sum.inl 1, 44683220090880000000), (Sum.inl 3, -89366440181760000000), (Sum.inl 5, 44683220090880000000), (Sum.inl 6, -11170805022720000000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, -268099320545280000000), (Sum.inl 35, -89366440181760000000), (Sum.inl 52, -89366440181760000000), (Sum.inl 59, 268099320545280000000), (Sum.inl 60, -89366440181760000000), (Sum.inl 128, -89366440181760000000)]

def reducedTerm67 : Integer.Sparse Master := [(Sum.inl 0, -48362801831608320000), (Sum.inl 1, 120907004579020800000), (Sum.inl 2, 181360506868531200000), (Sum.inl 6, 60453502289510400000), (Sum.inl 13, 322418678877388800000), (Sum.inl 60, 322418678877388800000), (Sum.inl 128, 322418678877388800000)]

def reducedTerm68 : Integer.Sparse Master := [(Sum.inl 0, 24575771049984000000), (Sum.inl 1, -55854025113600000000), (Sum.inl 2, -22341610045440000000), (Sum.inl 5, 134049660272640000000), (Sum.inl 59, 536198641090560000000)]

def reducedTerm69 : Integer.Sparse Master := [(Sum.inl 0, 24181400915804160000), (Sum.inl 1, -60453502289510400000), (Sum.inl 2, -60453502289510400000), (Sum.inl 6, 120907004579020800000), (Sum.inl 128, 483628018316083200000)]

def reducedTerm70 : Integer.Sparse Master := [(Sum.inl 0, 10647490723430400000), (Sum.inl 1, -17745817872384000000), (Sum.inl 2, -3549163574476800000), (Sum.inl 3, -56786617191628800000), (Sum.inl 5, -14196654297907200000), (Sum.inl 6, 3549163574476800000), (Sum.inl 35, -56786617191628800000), (Sum.inl 52, -56786617191628800000)]

def reducedTerm71 : Integer.Sparse Master := [(Sum.inl 0, -52616335203532800000), (Sum.inl 1, 105232670407065600000), (Sum.inl 2, 105232670407065600000), (Sum.inl 6, 52616335203532800000), (Sum.inl 52, -841861363256524800000)]

def reducedTerm72 : Integer.Sparse Master := [(Sum.inl 0, -6164405710848000000), (Sum.inl 1, 6164405710848000000), (Sum.inl 2, -24657622843392000000), (Sum.inl 5, -24657622843392000000), (Sum.inl 35, -98630491373568000000)]

def reducedTerm73 : Integer.Sparse Master := [(Sum.inl 0, -140515945472286720000), (Sum.inl 1, 267649419947212800000), (Sum.inl 2, 334561774934016000000), (Sum.inl 3, 2141195359577702400000), (Sum.inl 5, -1070597679788851200000), (Sum.inl 6, 100368532480204800000), (Sum.inl 7, 3211793039366553600000), (Sum.inl 8, 1070597679788851200000), (Sum.inl 9, -267649419947212800000), (Sum.inl 26, 535298839894425600000), (Sum.inl 35, 4282390719155404800000), (Sum.inl 52, 535298839894425600000), (Sum.inl 67, 1070597679788851200000), (Sum.inl 69, 2141195359577702400000), (Sum.inl 70, 2141195359577702400000), (Sum.inl 71, 535298839894425600000), (Sum.inl 257, 535298839894425600000)]

def reducedTerm74 : Integer.Sparse Master := [(Sum.inl 0, -99671615459942400000), (Sum.inl 1, 99671615459942400000), (Sum.inl 2, -348850654109798400000), (Sum.inl 9, 398686461839769600000), (Sum.inl 58, -49835807729971200000)]

def reducedTerm75 : Integer.Sparse Master := [(Sum.inl 0, 109701224427110400000), (Sum.inl 1, -137126530533888000000), (Sum.inl 2, 246827754960998400000), (Sum.inl 5, -548506122135552000000), (Sum.inl 6, 54850612213555200000), (Sum.inl 7, 877609795416883200000), (Sum.inl 8, 438804897708441600000), (Sum.inl 9, -219402448854220800000), (Sum.inl 35, 438804897708441600000), (Sum.inl 52, 438804897708441600000), (Sum.inl 69, 877609795416883200000), (Sum.inl 70, 438804897708441600000), (Sum.inl 71, 438804897708441600000)]

def reducedTerm76 : Integer.Sparse Master := [(Sum.inl 0, 48552198437191680000), (Sum.inl 1, -99311314985164800000), (Sum.inl 2, -44138362215628800000), (Sum.inl 5, -132415086646886400000), (Sum.inl 6, 33103771661721600000), (Sum.inl 7, 353106897725030400000), (Sum.inl 9, -88276724431257600000), (Sum.inl 35, 529660346587545600000), (Sum.inl 67, 176553448862515200000), (Sum.inl 69, 176553448862515200000), (Sum.inl 70, 353106897725030400000), (Sum.inl 257, 176553448862515200000)]

def reducedTerm77 : Integer.Sparse Master := [(Sum.inl 0, 37545455677685760000), (Sum.inl 1, -97100316407808000000), (Sum.inl 2, -71206898699059200000), (Sum.inl 3, -207147341669990400000), (Sum.inl 5, 258934177087488000000), (Sum.inl 6, -25893417708748800000), (Sum.inl 7, -414294683339980800000), (Sum.inl 8, -414294683339980800000), (Sum.inl 9, -103573670834995200000), (Sum.inl 35, -207147341669990400000), (Sum.inl 58, 6473354427187200000), (Sum.inl 69, -207147341669990400000), (Sum.inl 70, -103573670834995200000), (Sum.inl 71, -207147341669990400000)]

def reducedTerm78 : Integer.Sparse Master := [(Sum.inl 0, -461149994188800000), (Sum.inl 1, 999158320742400000), (Sum.inl 2, 538008326553600000), (Sum.inl 5, 614866658918400000), (Sum.inl 6, -538008326553600000), (Sum.inl 7, -1229733317836800000), (Sum.inl 35, -2459466635673600000), (Sum.inl 58, 76858332364800000), (Sum.inl 70, -1229733317836800000)]

def reducedTerm79 : Integer.Sparse Master := [(Sum.inl 0, 34956113906810880000), (Sum.inl 1, -45313480990310400000), (Sum.inl 2, 64733544271872000000), (Sum.inl 6, 32366772135936000000), (Sum.inl 8, 103573670834995200000), (Sum.inl 58, -6473354427187200000), (Sum.inl 71, 103573670834995200000)]

def reducedTerm80 : Integer.Sparse Master := [(Sum.inl 0, -135411930372096000000), (Sum.inl 1, 169264912965120000000), (Sum.inl 2, -406235791116288000000), (Sum.inl 3, -541647721488384000000), (Sum.inl 5, 270823860744192000000), (Sum.inl 6, -135411930372096000000), (Sum.inl 7, -541647721488384000000), (Sum.inl 9, -135411930372096000000), (Sum.inl 35, -1083295442976768000000), (Sum.inl 52, -1083295442976768000000), (Sum.inl 58, 33852982593024000000), (Sum.inl 69, -541647721488384000000), (Sum.inl 495, -541647721488384000000)]

def reducedTerm81 : Integer.Sparse Master := [(Sum.inl 0, -4717463735255040000), (Sum.inl 1, 12865810187059200000), (Sum.inl 2, 8577206791372800000), (Sum.inl 3, -17154413582745600000), (Sum.inl 6, 2144301697843200000), (Sum.inl 7, -34308827165491200000), (Sum.inl 9, -8577206791372800000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -68617654330982400000), (Sum.inl 67, -34308827165491200000), (Sum.inl 70, -17154413582745600000), (Sum.inl 257, -17154413582745600000)]

def reducedTerm82 : Integer.Sparse Master := [(Sum.inl 0, 64626493998366720000), (Sum.inl 1, -107710823330611200000), (Sum.inl 2, 47871477035827200000), (Sum.inl 5, -191485908143308800000), (Sum.inl 6, -23935738517913600000), (Sum.inl 7, 382971816286617600000), (Sum.inl 8, 382971816286617600000), (Sum.inl 9, 95742954071654400000), (Sum.inl 69, 191485908143308800000), (Sum.inl 71, 191485908143308800000)]

def reducedTerm83 : Integer.Sparse Master := [(Sum.inl 0, -5070089036759040000), (Sum.inl 1, -44363279071641600000), (Sum.inl 2, -4753208471961600000), (Sum.inl 3, 76051335551385600000), (Sum.inl 5, 12675222591897600000), (Sum.inl 9, 25350445183795200000), (Sum.inl 35, 50700890367590400000), (Sum.inl 58, -1584402823987200000), (Sum.inl 69, 76051335551385600000), (Sum.inl 70, 50700890367590400000)]

def reducedTerm84 : Integer.Sparse Master := [(Sum.inl 0, 5070089036759040000), (Sum.inl 1, 34856862127718400000), (Sum.inl 2, -3168805647974400000), (Sum.inl 5, 25350445183795200000), (Sum.inl 6, 4753208471961600000), (Sum.inl 7, 25350445183795200000), (Sum.inl 58, -1584402823987200000), (Sum.inl 69, 25350445183795200000)]

def reducedTerm85 : Integer.Sparse Master := [(Sum.inl 0, -112106736183214080000), (Sum.inl 1, -407660858848051200000), (Sum.inl 3, -407660858848051200000), (Sum.inl 5, 101915214712012800000), (Sum.inl 6, 50957607356006400000), (Sum.inl 9, -203830429424025600000), (Sum.inl 35, -407660858848051200000), (Sum.inl 69, -407660858848051200000), (Sum.inl 70, -407660858848051200000)]

def reducedTerm86 : Integer.Sparse Master := [(Sum.inl 0, -28026684045803520000), (Sum.inl 1, -114654616551014400000), (Sum.inl 2, -12739401839001600000), (Sum.inl 5, 101915214712012800000), (Sum.inl 6, 25478803678003200000), (Sum.inl 9, -50957607356006400000), (Sum.inl 58, -12739401839001600000)]

def reducedTerm87 : Integer.Sparse Master := [(Sum.inl 0, 135411930372096000000), (Sum.inl 1, -304676843337216000000), (Sum.inl 2, 33852982593024000000), (Sum.inl 3, 541647721488384000000), (Sum.inl 5, -135411930372096000000), (Sum.inl 6, -67705965186048000000), (Sum.inl 7, 1083295442976768000000), (Sum.inl 8, 541647721488384000000), (Sum.inl 9, 270823860744192000000), (Sum.inl 35, 541647721488384000000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000)]

def reducedTerm88 : Integer.Sparse Master := [(Sum.inl 0, -21722651632926720000), (Sum.inl 1, -81459943623475200000), (Sum.inl 2, 18102209694105600000), (Sum.inl 5, 36204419388211200000), (Sum.inl 6, -9051104847052800000), (Sum.inl 7, 144817677552844800000), (Sum.inl 9, 36204419388211200000), (Sum.inl 35, 144817677552844800000), (Sum.inl 70, 144817677552844800000)]

def reducedTerm89 : Integer.Sparse Master := [(Sum.inl 0, -36250784792248320000), (Sum.inl 1, 77680253126246400000), (Sum.inl 2, -12946708854374400000), (Sum.inl 6, -12946708854374400000), (Sum.inl 8, 207147341669990400000), (Sum.inl 9, 51786835417497600000), (Sum.inl 71, 207147341669990400000)]

def reducedTerm90 : Integer.Sparse Master := [(Sum.inl 0, -36997153171292160000), (Sum.inl 1, -151351990246195200000), (Sum.inl 2, -16816887805132800000), (Sum.inl 6, -16816887805132800000), (Sum.inl 7, 269070204882124800000), (Sum.inl 9, 67267551220531200000), (Sum.inl 69, 269070204882124800000)]

def reducedTerm91 : Integer.Sparse Master := [(Sum.inl 0, 14812828578938880000), (Sum.inl 1, -37032071447347200000), (Sum.inl 2, -30860059539456000000), (Sum.inl 5, -24688047631564800000), (Sum.inl 6, 6172011907891200000), (Sum.inl 9, -24688047631564800000), (Sum.inl 35, -98752190526259200000), (Sum.inl 67, -98752190526259200000), (Sum.inl 257, -98752190526259200000)]

def reducedTerm92 : Integer.Sparse Master := [(Sum.inl 0, 156671595988992000000), (Sum.inl 1, -235007393983488000000), (Sum.inl 2, 235007393983488000000), (Sum.inl 5, 626686383955968000000), (Sum.inl 8, 626686383955968000000), (Sum.inl 35, 1253372767911936000000), (Sum.inl 67, 626686383955968000000)]

def reducedTerm93 : Integer.Sparse Master := [(Sum.inl 0, 132808643070566400000), (Sum.inl 1, -265617286141132800000), (Sum.inl 5, -531234572282265600000), (Sum.inl 6, 664043215352832000000)]

def reducedTerm94 : Integer.Sparse Master := [(Sum.inl 0, -266409355871232000000), (Sum.inl 1, 444015593118720000000), (Sum.inl 2, -444015593118720000000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 986701318041600000000), (Sum.inl 6, -148005197706240000000), (Sum.inl 7, -1578722108866560000000), (Sum.inl 8, -789361054433280000000), (Sum.inl 35, -789361054433280000000)]

def reducedTerm95 : Integer.Sparse Master := [(Sum.inl 0, 24454770020352000000), (Sum.inl 1, -57061130047488000000), (Sum.inl 2, -32606360027136000000), (Sum.inl 5, 32606360027136000000), (Sum.inl 6, -32606360027136000000), (Sum.inl 35, -130425440108544000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm640 : Integer.Sparse Master := [(Sum.inr 1502, -1423280520010137600000)]

def reducedTerm641 : Integer.Sparse Master := [(Sum.inr 1504, -1951341470849433600000)]

def reducedTerm642 : Integer.Sparse Master := [(Sum.inr 1505, 1056230257065984000000)]

def reducedTerm643 : Integer.Sparse Master := [(Sum.inr 1508, 1423280520010137600000)]

def reducedTerm644 : Integer.Sparse Master := [(Sum.inr 1510, -2210913934743306240000)]

def reducedTerm645 : Integer.Sparse Master := [(Sum.inr 1511, -2862630613510520832000)]

def reducedTerm646 : Integer.Sparse Master := [(Sum.inr 1512, -1812234680041734144000)]

def reducedTerm647 : Integer.Sparse Master := [(Sum.inr 1513, 807931683631005696000)]

def reducedTerm648 : Integer.Sparse Master := [(Sum.inr 1514, 279082176459964416000)]

def reducedTerm649 : Integer.Sparse Master := [(Sum.inr 1515, 1951341470849433600000)]

def reducedTerm650 : Integer.Sparse Master := [(Sum.inr 1516, 1532149313286832128000)]

def reducedTerm651 : Integer.Sparse Master := [(Sum.inr 1520, 3125626258862112768000)]

def reducedTerm652 : Integer.Sparse Master := [(Sum.inr 1522, 1398340775856439296000)]

def reducedTerm653 : Integer.Sparse Master := [(Sum.inr 1523, 1978196107527585792000)]

def reducedTerm654 : Integer.Sparse Master := [(Sum.inr 1526, 3237439447258103808000)]

def reducedTerm655 : Integer.Sparse Master := [(Sum.inr 1528, -115736953684230144000)]

def reducedTerm656 : Integer.Sparse Master := [(Sum.inr 1529, -190397481621258240000)]

def reducedTerm657 : Integer.Sparse Master := [(Sum.inr 1530, -179029231679176704000)]

def reducedTerm658 : Integer.Sparse Master := [(Sum.inr 1531, -24315273996926976000)]

def reducedTerm659 : Integer.Sparse Master := [(Sum.inr 1532, 513372727945986048000)]

def reducedTerm660 : Integer.Sparse Master := [(Sum.inr 1533, 3726326584597413888000)]

def reducedTerm661 : Integer.Sparse Master := [(Sum.inr 1534, 92042023309737984000)]

def reducedTerm662 : Integer.Sparse Master := [(Sum.inr 1540, 299269579737268224000)]

def reducedTerm663 : Integer.Sparse Master := [(Sum.inr 1667, -1090667657931522048000)]

def reducedTerm664 : Integer.Sparse Master := [(Sum.inr 1668, -1101980502152183808000)]

def reducedTerm665 : Integer.Sparse Master := [(Sum.inr 1670, -735052166107693056000)]

def reducedTerm666 : Integer.Sparse Master := [(Sum.inr 1672, -615325865037004800000)]

def reducedTerm667 : Integer.Sparse Master := [(Sum.inr 1676, 441343231347916800000)]

def reducedTerm668 : Integer.Sparse Master := [(Sum.inr 1678, 2798915153550114816000)]

def reducedTerm669 : Integer.Sparse Master := [(Sum.inr 1679, 4204277593279561728000)]

def reducedTerm670 : Integer.Sparse Master := [(Sum.inr 1682, 4390161007521300480000)]

def reducedTerm671 : Integer.Sparse Master := [(Sum.inr 1684, 604529641244196864000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm672 : Integer.Sparse Master := [(Sum.inr 1685, 910860777696264192000)]

def reducedTerm673 : Integer.Sparse Master := [(Sum.inr 1686, 789405404560883712000)]

def reducedTerm674 : Integer.Sparse Master := [(Sum.inr 1687, -120789168095232000000)]

def reducedTerm675 : Integer.Sparse Master := [(Sum.inr 1688, 1305313133883752448000)]

def reducedTerm676 : Integer.Sparse Master := [(Sum.inr 1689, 3666193326655340544000)]

def reducedTerm677 : Integer.Sparse Master := [(Sum.inr 1695, 888021087364841472000)]

def reducedTerm678 : Integer.Sparse Master := [(Sum.inr 1697, 550098197290156032000)]

def reducedTerm679 : Integer.Sparse Master := [(Sum.inr 1699, -902368496446341120000)]

def reducedTerm680 : Integer.Sparse Master := [(Sum.inr 1700, -1069052130648391680000)]

def reducedTerm681 : Integer.Sparse Master := [(Sum.inr 1703, 2007627038014832640000)]

def reducedTerm682 : Integer.Sparse Master := [(Sum.inr 1704, 583395049348005888000)]

def reducedTerm683 : Integer.Sparse Master := [(Sum.inr 1709, -2010373847085219840000)]

def reducedTerm684 : Integer.Sparse Master := [(Sum.inr 1711, -4752834733161381888000)]

def reducedTerm685 : Integer.Sparse Master := [(Sum.inr 1712, -4818691431020888064000)]

def reducedTerm686 : Integer.Sparse Master := [(Sum.inr 1713, -3378878307861331968000)]

def reducedTerm687 : Integer.Sparse Master := [(Sum.inr 1714, -6227807807028068352000)]

def reducedTerm688 : Integer.Sparse Master := [(Sum.inr 1715, -2138368756797407232000)]

def reducedTerm689 : Integer.Sparse Master := [(Sum.inr 1716, 1926014843785052160000)]

def reducedTerm690 : Integer.Sparse Master := [(Sum.inr 1720, -1541521449311993856000)]

def reducedTerm691 : Integer.Sparse Master := [(Sum.inr 1721, 1386207265990901760000)]

def reducedTerm692 : Integer.Sparse Master := [(Sum.inr 1722, 1717512314662158336000)]

def reducedTerm693 : Integer.Sparse Master := [(Sum.inr 1723, -4810412754357977088000)]

def reducedTerm694 : Integer.Sparse Master := [(Sum.inr 1729, 3751773612556419072000)]

def reducedTerm695 : Integer.Sparse Master := [(Sum.inr 1734, -95615204742070272000)]

def reducedTerm696 : Integer.Sparse Master := [(Sum.inr 1735, 2302759193699155968000)]

def reducedTerm697 : Integer.Sparse Master := [(Sum.inr 1736, 2459234748121546752000)]

def reducedTerm698 : Integer.Sparse Master := [(Sum.inr 1740, 4524755554931834880000)]

def reducedTerm699 : Integer.Sparse Master := [(Sum.inr 1742, 119212994511765504000)]

def reducedTerm700 : Integer.Sparse Master := [(Sum.inr 1743, -8626840581832704000)]

def reducedTerm701 : Integer.Sparse Master := [(Sum.inr 1744, -554123003977138176000)]

def reducedTerm702 : Integer.Sparse Master := [(Sum.inr 1745, -2769188286440669184000)]

def reducedTerm703 : Integer.Sparse Master := [(Sum.inr 1746, -3563661364114489344000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm704 : Integer.Sparse Master := [(Sum.inr 1747, -1117582666619682816000)]

def reducedTerm705 : Integer.Sparse Master := [(Sum.inr 1748, 4393837063364345856000)]

def reducedTerm706 : Integer.Sparse Master := [(Sum.inr 1749, -722047208039055360000)]

def reducedTerm707 : Integer.Sparse Master := [(Sum.inr 1757, -474172475731476480000)]

def reducedTerm708 : Integer.Sparse Master := [(Sum.inr 1789, 654308882759024640000)]

def reducedTerm709 : Integer.Sparse Master := [(Sum.inr 1790, -4566900924634890240000)]

def reducedTerm710 : Integer.Sparse Master := [(Sum.inr 1791, -6742174334468751360000)]

def reducedTerm711 : Integer.Sparse Master := [(Sum.inr 1792, 2282493232765992960000)]

def reducedTerm712 : Integer.Sparse Master := [(Sum.inr 1793, 3731415152240885760000)]

def reducedTerm713 : Integer.Sparse Master := [(Sum.inr 1794, 673420605987225600000)]

def reducedTerm714 : Integer.Sparse Master := [(Sum.inr 1795, 8275744746720460800000)]

def reducedTerm715 : Integer.Sparse Master := [(Sum.inr 1796, 8393450481675141120000)]

def reducedTerm716 : Integer.Sparse Master := [(Sum.inr 1797, 5418404332170117120000)]

def reducedTerm717 : Integer.Sparse Master := [(Sum.inr 1802, 6265573704801976320000)]

def reducedTerm718 : Integer.Sparse Master := [(Sum.inr 1803, 28541892592926720000)]

def reducedTerm719 : Integer.Sparse Master := [(Sum.inr 1804, 2797448960684851200000)]

def reducedTerm720 : Integer.Sparse Master := [(Sum.inr 1805, 3885170543988572160000)]

def reducedTerm721 : Integer.Sparse Master := [(Sum.inr 1806, -9608222007357603840000)]

def reducedTerm722 : Integer.Sparse Master := [(Sum.inr 1807, 9318508415649054720000)]

def reducedTerm723 : Integer.Sparse Master := [(Sum.inr 1808, -4955053941050572800000)]

def reducedTerm724 : Integer.Sparse Master := [(Sum.inr 1809, -3537875996458352640000)]

def reducedTerm725 : Integer.Sparse Master := [(Sum.inr 1810, -3345967769848381440000)]

def reducedTerm726 : Integer.Sparse Master := [(Sum.inr 1811, 4908991524093296640000)]

def reducedTerm727 : Integer.Sparse Master := [(Sum.inr 1812, -11721265473473740800000)]

def reducedTerm728 : Integer.Sparse Master := [(Sum.inr 1813, 6324490501957877760000)]

def reducedTerm729 : Integer.Sparse Master := [(Sum.inr 1814, 2579448756790886400000)]

def reducedTerm730 : Integer.Sparse Master := [(Sum.inr 1815, -8001262491225292800000)]

def reducedTerm731 : Integer.Sparse Master := [(Sum.inr 1816, 8788236653722337280000)]

def reducedTerm732 : Integer.Sparse Master := [(Sum.inr 1817, -1747607698444124160000)]

def reducedTerm733 : Integer.Sparse Master := [(Sum.inr 1818, -7591910646227927040000)]

def reducedTerm734 : Integer.Sparse Master := [(Sum.inr 1819, -10541826291919749120000)]

def reducedTerm735 : Integer.Sparse Master := [(Sum.inr 1820, -629645571257794560000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm736 : Integer.Sparse Master := [(Sum.inr 1821, 1301309194638458880000)]

def reducedTerm737 : Integer.Sparse Master := [(Sum.inr 1822, 1098658614922444800000)]

def reducedTerm738 : Integer.Sparse Master := [(Sum.inr 1823, -1301309194638458880000)]

def reducedTerm739 : Integer.Sparse Master := [(Sum.inr 1824, 819808734353817600000)]

def reducedTerm740 : Integer.Sparse Master := [(Sum.inr 1825, 3329639154745344000000)]

def reducedTerm741 : Integer.Sparse Master := [(Sum.inr 1826, 2357878242882355200000)]

def reducedTerm742 : Integer.Sparse Master := [(Sum.inr 1827, -1098658614922444800000)]

def reducedTerm743 : Integer.Sparse Master := [(Sum.inr 1828, -750480790392668160000)]

def reducedTerm744 : Integer.Sparse Master := [(Sum.inr 1829, 6755524079380070400000)]

def reducedTerm745 : Integer.Sparse Master := [(Sum.inr 1830, 2387485449525657600000)]

def reducedTerm746 : Integer.Sparse Master := [(Sum.inr 1831, 4222772882708889600000)]

def reducedTerm747 : Integer.Sparse Master := [(Sum.inr 1832, -971893105435607040000)]

def reducedTerm748 : Integer.Sparse Master := [(Sum.inr 1957, -478232461800898560000)]

def reducedTerm749 : Integer.Sparse Master := [(Sum.inr 1964, -23934621521018880000)]

def reducedTerm750 : Integer.Sparse Master := [(Sum.inr 1965, 2241235474277990400000)]

def reducedTerm751 : Integer.Sparse Master := [(Sum.inr 1966, 5347929085248798720000)]

def reducedTerm752 : Integer.Sparse Master := [(Sum.inr 1967, 842806262366208000000)]

def reducedTerm753 : Integer.Sparse Master := [(Sum.inr 1970, 2206413845208760320000)]

def reducedTerm754 : Integer.Sparse Master := [(Sum.inr 1971, 3110224913045913600000)]

def reducedTerm755 : Integer.Sparse Master := [(Sum.inr 1973, 6990515310978662400000)]

def reducedTerm756 : Integer.Sparse Master := [(Sum.inr 1976, 2052530594103951360000)]

def reducedTerm757 : Integer.Sparse Master := [(Sum.inr 1977, -1235015743301222400000)]

def reducedTerm758 : Integer.Sparse Master := [(Sum.inr 1978, 4959624732475392000000)]

def reducedTerm759 : Integer.Sparse Master := [(Sum.inr 1979, 5755499567677440000000)]

def reducedTerm760 : Integer.Sparse Master := [(Sum.inr 1980, 5338073982173184000000)]

def reducedTerm761 : Integer.Sparse Master := [(Sum.inr 2010, -3936013149156802560000)]

def reducedTerm762 : Integer.Sparse Master := [(Sum.inr 2019, -2983567758946467840000)]

def reducedTerm763 : Integer.Sparse Master := [(Sum.inr 2020, 755963843883171840000)]

def reducedTerm764 : Integer.Sparse Master := [(Sum.inr 2022, 2983567758946467840000)]

def reducedTerm765 : Integer.Sparse Master := [(Sum.inr 2023, 88617370024673280000)]

def reducedTerm766 : Integer.Sparse Master := [(Sum.inr 2025, -4644957617419714560000)]

def reducedTerm767 : Integer.Sparse Master := [(Sum.inr 2026, 3018336835652812800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm768 : Integer.Sparse Master := [(Sum.inr 2028, 590858676786954240000)]

def reducedTerm769 : Integer.Sparse Master := [(Sum.inr 2029, -2441576368615587840000)]

def reducedTerm770 : Integer.Sparse Master := [(Sum.inr 2037, 4121680737526087680000)]

def reducedTerm771 : Integer.Sparse Master := [(Sum.inr 2039, 6300739362226176000000)]

def reducedTerm772 : Integer.Sparse Master := [(Sum.inr 2051, -2470341383010385920000)]

def reducedTerm773 : Integer.Sparse Master := [(Sum.inr 2054, 2470341383010385920000)]

def reducedTerm774 : Integer.Sparse Master := [(Sum.inr 2058, -2837840598442967040000)]

def reducedTerm775 : Integer.Sparse Master := [(Sum.inr 2062, -3893099630053294080000)]

def reducedTerm776 : Integer.Sparse Master := [(Sum.inr 2088, -2282493232765992960000)]

def reducedTerm777 : Integer.Sparse Master := [(Sum.inr 2089, -18920168420746199040000)]

def reducedTerm778 : Integer.Sparse Master := [(Sum.inr 2090, -27244411052347883520000)]

def reducedTerm779 : Integer.Sparse Master := [(Sum.inr 2092, 14205848185641369600000)]

def reducedTerm780 : Integer.Sparse Master := [(Sum.inr 2094, 15839955060530872320000)]

def reducedTerm781 : Integer.Sparse Master := [(Sum.inr 2104, -28541892592926720000)]

def reducedTerm782 : Integer.Sparse Master := [(Sum.inr 2105, -338218339097640960000)]

def reducedTerm783 : Integer.Sparse Master := [(Sum.inr 2106, 283347893291581440000)]

def reducedTerm784 : Integer.Sparse Master := [(Sum.inr 2107, 5704108413360537600000)]

def reducedTerm785 : Integer.Sparse Master := [(Sum.inr 2108, -18375094409940172800000)]

def reducedTerm786 : Integer.Sparse Master := [(Sum.inr 2109, 5542318650230046720000)]

def reducedTerm787 : Integer.Sparse Master := [(Sum.inr 2110, -14180570318501314560000)]

def reducedTerm788 : Integer.Sparse Master := [(Sum.inr 2112, -3684095090420613120000)]

def reducedTerm789 : Integer.Sparse Master := [(Sum.inr 2113, -757176972741181440000)]

def reducedTerm790 : Integer.Sparse Master := [(Sum.inr 2115, -12013936625481154560000)]

def reducedTerm791 : Integer.Sparse Master := [(Sum.inr 2116, -1563346111522406400000)]

def reducedTerm792 : Integer.Sparse Master := [(Sum.inr 2131, 1418945220960583680000)]

def reducedTerm793 : Integer.Sparse Master := [(Sum.inr 2132, -1418945220960583680000)]

def reducedTerm794 : Integer.Sparse Master := [(Sum.inr 2133, 11767743613933977600000)]

def reducedTerm795 : Integer.Sparse Master := [(Sum.inr 2134, 4056479869678387200000)]

def reducedTerm796 : Integer.Sparse Master := [(Sum.inr 2136, -40767630952366080000)]

def reducedTerm797 : Integer.Sparse Master := [(Sum.inr 2138, 8053752549762662400000)]

def reducedTerm798 : Integer.Sparse Master := [(Sum.inr 2140, -1056230257065984000000)]

def reducedTerm799 : Integer.Sparse Master := [(Sum.inr 2142, -1423280520010137600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm800 : Integer.Sparse Master := [(Sum.inr 2144, 1234719933093642240000)]

def reducedTerm801 : Integer.Sparse Master := [(Sum.inr 2145, 747433945254592512000)]

def reducedTerm802 : Integer.Sparse Master := [(Sum.inr 2146, -1041522169018318848000)]

def reducedTerm803 : Integer.Sparse Master := [(Sum.inr 2147, -1400262241941061632000)]

def reducedTerm804 : Integer.Sparse Master := [(Sum.inr 2148, -1951341470849433600000)]

def reducedTerm805 : Integer.Sparse Master := [(Sum.inr 2149, -3528479019960631296000)]

def reducedTerm806 : Integer.Sparse Master := [(Sum.inr 2153, -5084299705354813440000)]

def reducedTerm807 : Integer.Sparse Master := [(Sum.inr 2154, 415726753622261760000)]

def reducedTerm808 : Integer.Sparse Master := [(Sum.inr 2155, -199802494476877824000)]

def reducedTerm809 : Integer.Sparse Master := [(Sum.inr 2158, -1958086160293036032000)]

def reducedTerm810 : Integer.Sparse Master := [(Sum.inr 2160, 350247195718189056000)]

def reducedTerm811 : Integer.Sparse Master := [(Sum.inr 2161, 460809475344433152000)]

def reducedTerm812 : Integer.Sparse Master := [(Sum.inr 2162, 1082771078483017728000)]

def reducedTerm813 : Integer.Sparse Master := [(Sum.inr 2163, 104801980817866752000)]

def reducedTerm814 : Integer.Sparse Master := [(Sum.inr 2164, -4082980870490554368000)]

def reducedTerm815 : Integer.Sparse Master := [(Sum.inr 2171, -888215115745198080000)]

def reducedTerm816 : Integer.Sparse Master := [(Sum.inr 2172, -1086333153488142336000)]

def reducedTerm817 : Integer.Sparse Master := [(Sum.inr 2175, -2488877088999211008000)]

def reducedTerm818 : Integer.Sparse Master := [(Sum.inr 2176, -1039334509865336832000)]

def reducedTerm819 : Integer.Sparse Master := [(Sum.inr 2178, -2644281324676841472000)]

def reducedTerm820 : Integer.Sparse Master := [(Sum.inr 2179, 382802499623190528000)]

def reducedTerm821 : Integer.Sparse Master := [(Sum.inr 2180, 80987525421465600000)]

def reducedTerm822 : Integer.Sparse Master := [(Sum.inr 2181, -2480383209507323904000)]

def reducedTerm823 : Integer.Sparse Master := [(Sum.inr 2187, 1069052130648391680000)]

def reducedTerm824 : Integer.Sparse Master := [(Sum.inr 2189, -535625493262368768000)]

def reducedTerm825 : Integer.Sparse Master := [(Sum.inr 2192, 2550756900341809152000)]

def reducedTerm826 : Integer.Sparse Master := [(Sum.inr 2194, 506714469983059968000)]

def reducedTerm827 : Integer.Sparse Master := [(Sum.inr 2195, 2281683348482162688000)]

def reducedTerm828 : Integer.Sparse Master := [(Sum.inr 2196, 4171042250963288064000)]

def reducedTerm829 : Integer.Sparse Master := [(Sum.inr 2197, 3716334068831354880000)]

def reducedTerm830 : Integer.Sparse Master := [(Sum.inr 2198, -1758049717505163264000)]

def reducedTerm831 : Integer.Sparse Master := [(Sum.inr 2199, -529608735311265792000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm832 : Integer.Sparse Master := [(Sum.inr 2200, -2923000637003661312000)]

def reducedTerm833 : Integer.Sparse Master := [(Sum.inr 2201, -968581412641898496000)]

def reducedTerm834 : Integer.Sparse Master := [(Sum.inr 2207, -1075562447389065216000)]

def reducedTerm835 : Integer.Sparse Master := [(Sum.inr 2211, 3118020017674125312000)]

def reducedTerm836 : Integer.Sparse Master := [(Sum.inr 2212, 3417517613264928768000)]

def reducedTerm837 : Integer.Sparse Master := [(Sum.inr 2213, -164392035143712768000)]

def reducedTerm838 : Integer.Sparse Master := [(Sum.inr 2217, 6106405275203272704000)]

def reducedTerm839 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000)]

def reducedTerm840 : Integer.Sparse Master := [(Sum.inr 2220, 1698881328169353216000)]

def reducedTerm841 : Integer.Sparse Master := [(Sum.inr 2221, -2422443967567626240000)]

def reducedTerm842 : Integer.Sparse Master := [(Sum.inr 2222, -2652931479726194688000)]

def reducedTerm843 : Integer.Sparse Master := [(Sum.inr 2223, 454996272018161664000)]

def reducedTerm844 : Integer.Sparse Master := [(Sum.inr 2231, 522094469787942912000)]

def reducedTerm845 : Integer.Sparse Master := [(Sum.inr 2232, 825412766634344448000)]

def reducedTerm846 : Integer.Sparse Master := [(Sum.inr 2233, -7143996310767009792000)]

def reducedTerm847 : Integer.Sparse Master := [(Sum.inr 2234, 5281412168984297472000)]

def reducedTerm848 : Integer.Sparse Master := [(Sum.inr 2235, 8991466736109355008000)]

def reducedTerm849 : Integer.Sparse Master := [(Sum.inr 2238, 1167171979199643648000)]

def reducedTerm850 : Integer.Sparse Master := [(Sum.inr 2239, -11939427307487232000)]

def reducedTerm851 : Integer.Sparse Master := [(Sum.inr 2240, -912884097845035008000)]

def reducedTerm852 : Integer.Sparse Master := [(Sum.inr 2243, -3530220507746795520000)]

def reducedTerm853 : Integer.Sparse Master := [(Sum.inr 2244, -13288538835716014080000)]

def reducedTerm854 : Integer.Sparse Master := [(Sum.inr 2245, 5084282729677455360000)]

def reducedTerm855 : Integer.Sparse Master := [(Sum.inr 2246, 14561556817950277632000)]

def reducedTerm856 : Integer.Sparse Master := [(Sum.inr 2247, -12514908548880138240000)]

def reducedTerm857 : Integer.Sparse Master := [(Sum.inr 2248, -2840232254671945728000)]

def reducedTerm858 : Integer.Sparse Master := [(Sum.inr 2249, -2254308298937597952000)]

def reducedTerm859 : Integer.Sparse Master := [(Sum.inr 2250, 6385220328544468992000)]

def reducedTerm860 : Integer.Sparse Master := [(Sum.inr 2251, 6295106507412602880000)]

def reducedTerm861 : Integer.Sparse Master := [(Sum.inr 2252, -1717100482923528192000)]

def reducedTerm862 : Integer.Sparse Master := [(Sum.inr 2253, -11806284324964663296000)]

def reducedTerm863 : Integer.Sparse Master := [(Sum.inr 2254, 3977835312798498816000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm864 : Integer.Sparse Master := [(Sum.inr 2255, 13423761248418791424000)]

def reducedTerm865 : Integer.Sparse Master := [(Sum.inr 2256, -3060986888631877632000)]

def reducedTerm866 : Integer.Sparse Master := [(Sum.inr 2257, 356540332144066560000)]

def reducedTerm867 : Integer.Sparse Master := [(Sum.inr 2258, -285682392053710848000)]

def reducedTerm868 : Integer.Sparse Master := [(Sum.inr 2259, -2232992392359837696000)]

def reducedTerm869 : Integer.Sparse Master := [(Sum.inr 2262, 4747445379992125440000)]

def reducedTerm870 : Integer.Sparse Master := []

def reducedTerm871 : Integer.Sparse Master := []

def reducedTerm872 : Integer.Sparse Master := []

def reducedTerm873 : Integer.Sparse Master := [(Sum.inr 2266, -17198383075263774720000)]

def reducedTerm874 : Integer.Sparse Master := [(Sum.inr 2267, 2456191162674708480000)]

def reducedTerm875 : Integer.Sparse Master := []

def reducedTerm876 : Integer.Sparse Master := [(Sum.inr 2272, 620385158666649600000)]

def reducedTerm877 : Integer.Sparse Master := [(Sum.inr 2273, 1530801552859987968000)]

def reducedTerm878 : Integer.Sparse Master := [(Sum.inr 2274, 11930424302148452352000)]

def reducedTerm879 : Integer.Sparse Master := [(Sum.inr 2277, 7044709980352020480000)]

def reducedTerm880 : Integer.Sparse Master := [(Sum.inr 2278, 613475877389598720000)]

def reducedTerm881 : Integer.Sparse Master := [(Sum.inr 2279, 4948572573257564160000)]

def reducedTerm882 : Integer.Sparse Master := [(Sum.inr 2280, 4794515628466765824000)]

def reducedTerm883 : Integer.Sparse Master := [(Sum.inr 2281, 9591223123887390720000)]

def reducedTerm884 : Integer.Sparse Master := [(Sum.inr 2282, -328449504969621504000)]

def reducedTerm885 : Integer.Sparse Master := [(Sum.inr 2283, 1069657792115834880000)]

def reducedTerm886 : Integer.Sparse Master := [(Sum.inr 2284, 3942379037195698176000)]

def reducedTerm887 : Integer.Sparse Master := [(Sum.inr 2285, 88491352709136384000)]

def reducedTerm888 : Integer.Sparse Master := [(Sum.inr 2286, 1402778741635547136000)]

def reducedTerm889 : Integer.Sparse Master := []

def reducedTerm890 : Integer.Sparse Master := []

def reducedTerm891 : Integer.Sparse Master := [(Sum.inr 2294, -9942532690001264640000)]

def reducedTerm892 : Integer.Sparse Master := [(Sum.inr 2323, -5775400208422010880000)]

def reducedTerm893 : Integer.Sparse Master := [(Sum.inr 2327, 1409374911961497600000)]

def reducedTerm894 : Integer.Sparse Master := [(Sum.inr 2330, -1021462625098137600000)]

def reducedTerm895 : Integer.Sparse Master := [(Sum.inr 2332, 8792971061782118400000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm896 : Integer.Sparse Master := [(Sum.inr 2334, 1021462625098137600000)]

def reducedTerm897 : Integer.Sparse Master := [(Sum.inr 2337, 2042925250196275200000)]

def reducedTerm898 : Integer.Sparse Master := [(Sum.inr 2338, 6349509219129753600000)]

def reducedTerm899 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000)]

def reducedTerm900 : Integer.Sparse Master := [(Sum.inr 2340, -5831241247610634240000)]

def reducedTerm901 : Integer.Sparse Master := [(Sum.inr 2341, -4592195406267678720000)]

def reducedTerm902 : Integer.Sparse Master := [(Sum.inr 2342, -8792971061782118400000)]

def reducedTerm903 : Integer.Sparse Master := [(Sum.inr 2344, -1021462625098137600000)]

def reducedTerm904 : Integer.Sparse Master := [(Sum.inr 2345, -15267702809682247680000)]

def reducedTerm905 : Integer.Sparse Master := [(Sum.inr 2346, 3811111984406200320000)]

def reducedTerm906 : Integer.Sparse Master := [(Sum.inr 2347, 54778388874854400000)]

def reducedTerm907 : Integer.Sparse Master := [(Sum.inr 2348, -54778388874854400000)]

def reducedTerm908 : Integer.Sparse Master := [(Sum.inr 2349, -598839592845312000000)]

def reducedTerm909 : Integer.Sparse Master := [(Sum.inr 2350, -2122040394523607040000)]

def reducedTerm910 : Integer.Sparse Master := [(Sum.inr 2352, 14499441893476270080000)]

def reducedTerm911 : Integer.Sparse Master := [(Sum.inr 2353, -4008567374777548800000)]

def reducedTerm912 : Integer.Sparse Master := [(Sum.inr 2355, -3201531558440140800000)]

def reducedTerm913 : Integer.Sparse Master := [(Sum.inr 2356, 7210098933217689600000)]

def reducedTerm914 : Integer.Sparse Master := [(Sum.inr 2361, -4433171053215744000000)]

def reducedTerm915 : Integer.Sparse Master := [(Sum.inr 2362, -9916201969680384000000)]

def reducedTerm916 : Integer.Sparse Master := [(Sum.inr 2423, 5684917680995696640000)]

def reducedTerm917 : Integer.Sparse Master := [(Sum.inr 2425, -3022934715924480000000)]

def reducedTerm918 : Integer.Sparse Master := [(Sum.inr 2426, -2089015568665804800000)]

def reducedTerm919 : Integer.Sparse Master := [(Sum.inr 2428, 5559732986314752000000)]

def reducedTerm920 : Integer.Sparse Master := [(Sum.inr 2429, -3513264514950758400000)]

def reducedTerm921 : Integer.Sparse Master := [(Sum.inr 2430, 19962365120110264320000)]

def reducedTerm922 : Integer.Sparse Master := [(Sum.inr 2431, 14124724583912570880000)]

def reducedTerm923 : Integer.Sparse Master := [(Sum.inr 2432, 762973624782028800000)]

def reducedTerm924 : Integer.Sparse Master := [(Sum.inr 2433, 2089015568665804800000)]

def reducedTerm925 : Integer.Sparse Master := [(Sum.inr 2434, -4285922492777103360000)]

def reducedTerm926 : Integer.Sparse Master := [(Sum.inr 2435, 5339288646065848320000)]

def reducedTerm927 : Integer.Sparse Master := [(Sum.inr 2437, -29125569354242457600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm928 : Integer.Sparse Master := [(Sum.inr 2438, -4666690457468928000000)]

def reducedTerm929 : Integer.Sparse Master := [(Sum.inr 2440, -1089057424637952000000)]

def reducedTerm930 : Integer.Sparse Master := [(Sum.inr 2441, -27156418471526400000)]

def reducedTerm931 : Integer.Sparse Master := [(Sum.inr 2442, 4167404634193920000000)]

def reducedTerm932 : Integer.Sparse Master := [(Sum.inr 2443, -6201565287992524800000)]

def reducedTerm933 : Integer.Sparse Master := [(Sum.inr 2470, -669848715789926400000)]

def reducedTerm934 : Integer.Sparse Master := [(Sum.inr 2471, 5402275542460661760000)]

def reducedTerm935 : Integer.Sparse Master := [(Sum.inr 2473, 669848715789926400000)]

def reducedTerm936 : Integer.Sparse Master := [(Sum.inr 2479, -21951447043276800000)]

def reducedTerm937 : Integer.Sparse Master := [(Sum.inr 2480, -12811011857783193600000)]

def reducedTerm938 : Integer.Sparse Master := [(Sum.inr 2482, 3044886162967756800000)]

def reducedTerm939 : Integer.Sparse Master := [(Sum.inr 2483, 10730200326977617920000)]

def reducedTerm940 : Integer.Sparse Master := [(Sum.inr 2485, -7075268186112000000000)]

def reducedTerm941 : Integer.Sparse Master := [(Sum.inr 2486, -10132091952404889600000)]

def reducedTerm942 : Integer.Sparse Master := [(Sum.inr 2488, 3036144140609126400000)]

def reducedTerm943 : Integer.Sparse Master := [(Sum.inr 2489, 12048038233001164800000)]

def reducedTerm944 : Integer.Sparse Master := [(Sum.inr 2494, 882109921738752000000)]

def reducedTerm945 : Integer.Sparse Master := [(Sum.inr 2495, 421979070165811200000)]

def reducedTerm946 : Integer.Sparse Master := [(Sum.inr 2497, 2247947368157675520000)]

def reducedTerm947 : Integer.Sparse Master := [(Sum.inr 2499, -7786684812636979200000)]

def reducedTerm948 : Integer.Sparse Master := [(Sum.inr 2508, 4693700295180288000000)]

def reducedTerm949 : Integer.Sparse Master := [(Sum.inr 2512, -8251961190668697600000)]

def reducedTerm950 : Integer.Sparse Master := [(Sum.inr 2513, -4629005356695552000000)]

def reducedTerm951 : Integer.Sparse Master := [(Sum.inr 2515, 20072224660871577600000)]

def reducedTerm952 : Integer.Sparse Master := [(Sum.inr 2519, 4382870405576785920000)]

def reducedTerm953 : Integer.Sparse Master := [(Sum.inr 2520, 3829273250294661120000)]

def reducedTerm954 : Integer.Sparse Master := [(Sum.inr 2522, -46570423131832320000)]

def reducedTerm955 : Integer.Sparse Master := [(Sum.inr 2524, 94866766992506880000)]

def reducedTerm956 : Integer.Sparse Master := [(Sum.inr 2529, -1138001372530606080000)]

def reducedTerm957 : Integer.Sparse Master := [(Sum.inr 2545, -1139201814778675200000)]

def reducedTerm958 : Integer.Sparse Master := [(Sum.inr 2553, -5874441005529169920000)]

def reducedTerm959 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm96 : Integer.Sparse Master := [(Sum.inl 0, -25710705944985600000), (Sum.inl 1, 51421411889971200000), (Sum.inl 2, -64276764862464000000), (Sum.inl 3, -205685647559884800000), (Sum.inl 5, 77132117834956800000), (Sum.inl 6, -12855352972492800000), (Sum.inl 7, -205685647559884800000), (Sum.inl 26, -102842823779942400000), (Sum.inl 35, -308528471339827200000), (Sum.inl 52, -102842823779942400000), (Sum.inl 67, -102842823779942400000)]

def reducedTerm97 : Integer.Sparse Master := [(Sum.inl 0, 91984761166233600000), (Sum.inl 1, -229961902915584000000), (Sum.inl 2, -91984761166233600000), (Sum.inl 5, 183969522332467200000), (Sum.inl 6, -137977141749350400000), (Sum.inl 35, -735878089329868800000), (Sum.inl 52, -735878089329868800000)]

def reducedTerm98 : Integer.Sparse Master := [(Sum.inl 0, -120023540507566080000), (Sum.inl 1, 272780773880832000000), (Sum.inl 2, 109112309552332800000), (Sum.inl 5, -654673857313996800000), (Sum.inl 7, 872898476418662400000), (Sum.inl 35, 872898476418662400000), (Sum.inl 67, 872898476418662400000)]

def reducedTerm99 : Integer.Sparse Master := [(Sum.inl 0, 173005516409241600000), (Sum.inl 1, -370726106591232000000), (Sum.inl 5, 988602950909952000000), (Sum.inl 7, -988602950909952000000), (Sum.inl 8, -988602950909952000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm960 : Integer.Sparse Master := [(Sum.inr 2557, -827530229555527680000)]

def reducedTerm961 : Integer.Sparse Master := [(Sum.inr 2558, 3350500907776081920000)]

def reducedTerm962 : Integer.Sparse Master := [(Sum.inr 2560, -1308617765518049280000)]

def reducedTerm963 : Integer.Sparse Master := [(Sum.inr 2561, -8081533245759160320000)]

def reducedTerm964 : Integer.Sparse Master := [(Sum.inr 2566, 54778388874854400000)]

def reducedTerm965 : Integer.Sparse Master := [(Sum.inr 2569, -54778388874854400000)]

def reducedTerm966 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000)]

def reducedTerm967 : Integer.Sparse Master := [(Sum.inr 2575, 7730575112285061120000)]

def reducedTerm968 : Integer.Sparse Master := [(Sum.inr 2587, 2089015568665804800000)]

def reducedTerm969 : Integer.Sparse Master := [(Sum.inr 2589, -878316128737689600000)]

def reducedTerm970 : Integer.Sparse Master := [(Sum.inr 2590, 9764819380324270080000)]

def reducedTerm971 : Integer.Sparse Master := [(Sum.inr 2591, -2089015568665804800000)]

def reducedTerm972 : Integer.Sparse Master := [(Sum.inr 2600, 6525212987851407360000)]

def reducedTerm973 : Integer.Sparse Master := [(Sum.inr 2603, 4404201698619555840000)]

def reducedTerm974 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000)]

def reducedTerm975 : Integer.Sparse Master := [(Sum.inr 2617, -9280530725231001600000)]

def reducedTerm976 : Integer.Sparse Master := [(Sum.inr 2618, 34864691456596377600000)]

def reducedTerm977 : Integer.Sparse Master := [(Sum.inr 2620, 10563661873945313280000)]

def reducedTerm978 : Integer.Sparse Master := [(Sum.inr 2631, -15111984861079142400000)]

def reducedTerm979 : Integer.Sparse Master := [(Sum.inr 2632, -6403063116880281600000)]

def reducedTerm980 : Integer.Sparse Master := [(Sum.inr 2633, 15111984861079142400000)]

def reducedTerm981 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000)]

def reducedTerm982 : Integer.Sparse Master := [(Sum.inr 2641, 7417350658916352000000)]

def reducedTerm983 : Integer.Sparse Master := [(Sum.inr 2643, 7685347844476108800000)]

def reducedTerm984 : Integer.Sparse Master := [(Sum.inr 2652, 4097268088154357760000)]

def reducedTerm985 : Integer.Sparse Master := [(Sum.inr 2653, -2900413559198711808000)]

def reducedTerm986 : Integer.Sparse Master := [(Sum.inr 2654, -59568121389514752000)]

def reducedTerm987 : Integer.Sparse Master := [(Sum.inr 2655, 414737902356922368000)]

def reducedTerm988 : Integer.Sparse Master := [(Sum.inr 2656, 2451504521281536000000)]

def reducedTerm989 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000)]

def reducedTerm990 : Integer.Sparse Master := [(Sum.inr 2658, -31848465594580992000)]

def reducedTerm991 : Integer.Sparse Master := [(Sum.inr 2659, -4218827410224709632000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm992 : Integer.Sparse Master := [(Sum.inr 2661, 2542985543602667520000)]

def reducedTerm993 : Integer.Sparse Master := [(Sum.inr 2662, -95323232121126912000)]

def reducedTerm994 : Integer.Sparse Master := [(Sum.inr 2664, 888215115745198080000)]

def reducedTerm995 : Integer.Sparse Master := [(Sum.inr 2669, 1951341470849433600000)]

def reducedTerm996 : Integer.Sparse Master := [(Sum.inr 2670, -4302905736953069568000)]

def reducedTerm997 : Integer.Sparse Master := [(Sum.inr 2673, 3169748139186585600000)]

def reducedTerm998 : Integer.Sparse Master := [(Sum.inr 2676, 2197036481036156928000)]

def reducedTerm999 : Integer.Sparse Master := [(Sum.inr 2677, 3660221256271921152000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm282 : Integer.Sparse Master := [(Sum.inl 0, 19499786217676800000), (Sum.inl 1, -3362032106496000000), (Sum.inl 3, 161377541111808000000), (Sum.inl 4, 107585027407872000000), (Sum.inl 5, 13448128425984000000), (Sum.inl 26, 107585027407872000000), (Sum.inl 27, -40344385277952000000), (Sum.inl 35, 53792513703936000000), (Sum.inl 55, -161377541111808000000)]

def reducedTerm283 : Integer.Sparse Master := [(Sum.inl 0, 82917618300518400000), (Sum.inl 1, -165835236601036800000), (Sum.inl 2, -82917618300518400000), (Sum.inl 27, 331670473202073600000), (Sum.inl 55, 1326681892808294400000)]

def reducedTerm284 : Integer.Sparse Master := [(Sum.inl 0, -278981671152844800000), (Sum.inl 1, -1634035502466662400000), (Sum.inl 2, -318836195603251200000), (Sum.inl 3, 4463706738445516800000), (Sum.inl 4, 2550689564826009600000), (Sum.inl 5, 159418097801625600000), (Sum.inl 26, 2550689564826009600000), (Sum.inl 27, -478254293404876800000), (Sum.inl 35, 637672391206502400000), (Sum.inl 55, -1913017173619507200000)]

def reducedTerm285 : Integer.Sparse Master := [(Sum.inl 0, -5993222226647040000), (Sum.inl 1, -24517727290828800000), (Sum.inl 2, 21793535369625600000), (Sum.inl 3, 130761212217753600000), (Sum.inl 12, 87174141478502400000), (Sum.inl 13, 217935353696256000000), (Sum.inl 26, 87174141478502400000), (Sum.inl 34, 87174141478502400000)]

def reducedTerm287 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm288 : Integer.Sparse Master := [(Sum.inl 0, -38196356146421760000), (Sum.inl 1, -494305785424281600000), (Sum.inl 2, 33702667188019200000), (Sum.inl 3, 898737791680512000000), (Sum.inl 4, 359495116672204800000), (Sum.inl 26, 359495116672204800000)]

def reducedTerm289 : Integer.Sparse Master := [(Sum.inl 0, 34075822114897920000), (Sum.inl 1, -35078052177100800000), (Sum.inl 2, -45100352799129600000), (Sum.inl 3, 80178404976230400000), (Sum.inl 26, 80178404976230400000)]

def reducedTerm290 : Integer.Sparse Master := [(Sum.inl 0, 157071668576256000000), (Sum.inl 1, -108325288673280000000), (Sum.inl 2, -189569255178240000000), (Sum.inl 3, 433301154693120000000)]

def reducedTerm291 : Integer.Sparse Master := [(Sum.inl 0, 14907895382016000000), (Sum.inl 2, 74539476910080000000)]

def reducedTerm292 : Integer.Sparse Master := [(Sum.inl 0, -89856815195750400000), (Sum.inl 1, -260874624761856000000), (Sum.inl 2, -28986069417984000000), (Sum.inl 3, 3014551219470336000000), (Sum.inl 4, 927554221375488000000), (Sum.inl 5, 115944277671936000000), (Sum.inl 6, -14493034708992000000), (Sum.inl 12, 927554221375488000000), (Sum.inl 13, 1391331332063232000000), (Sum.inl 26, 1391331332063232000000), (Sum.inl 27, -173916416507904000000), (Sum.inl 33, -1391331332063232000000), (Sum.inl 34, 927554221375488000000), (Sum.inl 35, 231888555343872000000), (Sum.inl 54, -695665666031616000000), (Sum.inl 65, -695665666031616000000), (Sum.inl 67, 231888555343872000000)]

def reducedTerm293 : Integer.Sparse Master := [(Sum.inl 0, -32936230279249920000), (Sum.inl 1, 75478861056614400000), (Sum.inl 2, 48032002490572800000), (Sum.inl 3, -109787434264166400000), (Sum.inl 5, -27446858566041600000), (Sum.inl 26, -109787434264166400000), (Sum.inl 27, 82340575698124800000), (Sum.inl 33, 329362302792499200000), (Sum.inl 54, 329362302792499200000), (Sum.inl 65, 329362302792499200000)]

def reducedTerm294 : Integer.Sparse Master := [(Sum.inl 0, 28689446544998400000), (Sum.inl 1, 317633158176768000000), (Sum.inl 2, -71723616362496000000), (Sum.inl 3, -1967276334514176000000), (Sum.inl 4, -327879389085696000000), (Sum.inl 12, -983638167257088000000), (Sum.inl 13, -1147577861799936000000), (Sum.inl 26, -327879389085696000000), (Sum.inl 33, 983638167257088000000), (Sum.inl 34, -327879389085696000000)]

def reducedTerm295 : Integer.Sparse Master := [(Sum.inl 0, -32568193179648000000), (Sum.inl 1, 13570080491520000000), (Sum.inl 2, 13570080491520000000), (Sum.inl 3, -434242575728640000000), (Sum.inl 12, -217121287864320000000), (Sum.inl 13, -434242575728640000000), (Sum.inl 33, 651363863592960000000)]

def reducedTerm296 : Integer.Sparse Master := [(Sum.inl 0, 6752906641152000000), (Sum.inl 1, -26656210425600000000), (Sum.inl 3, 85299873361920000000), (Sum.inl 12, 56866582241280000000), (Sum.inl 13, 113733164482560000000), (Sum.inl 34, 28433291120640000000)]

def reducedTerm297 : Integer.Sparse Master := [(Sum.inl 0, -2795891057971200000), (Sum.inl 1, 8387673173913600000), (Sum.inl 2, -16775346347827200000), (Sum.inl 13, 44734256927539200000)]

def reducedTerm298 : Integer.Sparse Master := [(Sum.inl 0, 50423918195589120000), (Sum.inl 1, 58181444071833600000), (Sum.inl 2, -77575258762444800000), (Sum.inl 3, 930903105149337600000), (Sum.inl 13, 310301035049779200000), (Sum.inl 26, 620602070099558400000), (Sum.inl 34, 620602070099558400000)]

def reducedTerm299 : Integer.Sparse Master := [(Sum.inl 0, 670226695917649920000), (Sum.inl 1, -197125498799308800000), (Sum.inl 2, 788501995197235200000), (Sum.inl 3, 3154007980788940800000), (Sum.inl 4, 1577003990394470400000), (Sum.inl 26, 1577003990394470400000)]

def reducedTerm300 : Integer.Sparse Master := [(Sum.inl 0, -85188233869885440000), (Sum.inl 1, 67253868844646400000), (Sum.inl 2, 89671825126195200000), (Sum.inl 26, 358687300504780800000)]

def reducedTerm301 : Integer.Sparse Master := []

def reducedTerm302 : Integer.Sparse Master := [(Sum.inl 0, -244513839981035520000), (Sum.inl 1, 514765978907443200000), (Sum.inl 2, 321728736817152000000), (Sum.inl 3, 1029531957814886400000)]

def reducedTerm303 : Integer.Sparse Master := [(Sum.inl 0, 58866405003141120000), (Sum.inl 1, -214059654556876800000), (Sum.inl 2, -133787284098048000000), (Sum.inl 3, -428119309113753600000), (Sum.inl 13, -428119309113753600000), (Sum.inl 34, -428119309113753600000)]

def reducedTerm304 : Integer.Sparse Master := [(Sum.inl 0, 3410974922342400000), (Sum.inl 1, 3410974922342400000), (Sum.inl 2, 11369916407808000000), (Sum.inl 3, -109151197514956800000), (Sum.inl 4, -36383732504985600000), (Sum.inl 5, -6821949844684800000), (Sum.inl 13, -18191866252492800000), (Sum.inl 26, -109151197514956800000), (Sum.inl 27, 20465849534054400000), (Sum.inl 34, -72767465009971200000), (Sum.inl 65, 27287799378739200000), (Sum.inl 66, 54575598757478400000), (Sum.inl 67, -27287799378739200000)]

def reducedTerm305 : Integer.Sparse Master := [(Sum.inl 0, 43373623167221760000), (Sum.inl 1, -9036171493171200000), (Sum.inl 2, -45180857465856000000), (Sum.inl 3, 289157487781478400000), (Sum.inl 5, 36144685972684800000), (Sum.inl 13, 144578743890739200000), (Sum.inl 26, 289157487781478400000), (Sum.inl 27, -108434057918054400000), (Sum.inl 34, 289157487781478400000), (Sum.inl 65, -433736231672217600000), (Sum.inl 67, 144578743890739200000)]

def reducedTerm306 : Integer.Sparse Master := [(Sum.inl 0, -3004478871367680000), (Sum.inl 1, -338003873028864000000), (Sum.inl 2, 97645563319449600000), (Sum.inl 3, 1562329013111193600000), (Sum.inl 4, 721074929128243200000), (Sum.inl 12, 120179154854707200000), (Sum.inl 13, 120179154854707200000), (Sum.inl 26, 841254083982950400000), (Sum.inl 33, -360537464564121600000), (Sum.inl 34, 240358309709414400000)]

def reducedTerm307 : Integer.Sparse Master := [(Sum.inl 0, 20807403366758400000), (Sum.inl 1, 166459226934067200000), (Sum.inl 2, -62422210100275200000), (Sum.inl 3, 665836907736268800000), (Sum.inl 26, 332918453868134400000), (Sum.inl 33, -998755361604403200000)]

def reducedTerm308 : Integer.Sparse Master := []

def reducedTerm309 : Integer.Sparse Master := [(Sum.inl 0, 30907674458357760000), (Sum.inl 1, -94440116400537600000), (Sum.inl 2, -42927325636608000000), (Sum.inl 3, 274734884074291200000), (Sum.inl 12, 137367442037145600000), (Sum.inl 13, 137367442037145600000)]

def reducedTerm310 : Integer.Sparse Master := [(Sum.inl 0, -40139902107648000000), (Sum.inl 1, 66899836846080000000), (Sum.inl 2, 66899836846080000000), (Sum.inl 3, -133799673692160000000), (Sum.inl 5, -33449918423040000000), (Sum.inl 12, -133799673692160000000), (Sum.inl 13, -133799673692160000000), (Sum.inl 27, 100349755269120000000), (Sum.inl 33, 401399021076480000000), (Sum.inl 55, 401399021076480000000), (Sum.inl 61, 401399021076480000000)]

def reducedTerm311 : Integer.Sparse Master := [(Sum.inl 0, -5002763219435520000), (Sum.inl 1, -15917882970931200000), (Sum.inl 2, -4547966563123200000), (Sum.inl 3, -36383732504985600000), (Sum.inl 4, -18191866252492800000), (Sum.inl 5, -4547966563123200000), (Sum.inl 26, -54575598757478400000), (Sum.inl 27, 13643899689369600000), (Sum.inl 34, -36383732504985600000), (Sum.inl 66, 54575598757478400000), (Sum.inl 67, -18191866252492800000)]

def reducedTerm312 : Integer.Sparse Master := [(Sum.inl 0, -37360588929269760000), (Sum.inl 1, -33964171753881600000), (Sum.inl 2, -84910429384704000000), (Sum.inl 3, -1086853496124211200000), (Sum.inl 4, -543426748062105600000), (Sum.inl 26, -815140122093158400000), (Sum.inl 34, -271713374031052800000)]

def reducedTerm313 : Integer.Sparse Master := [(Sum.inl 0, 19026756426424320000), (Sum.inl 2, 22650900507648000000), (Sum.inl 3, 217448644873420800000), (Sum.inl 4, 144965763248947200000), (Sum.inl 26, 144965763248947200000)]

def reducedTerm314 : Integer.Sparse Master := [(Sum.inl 0, -388858243608576000000), (Sum.inl 1, 694389720729600000000), (Sum.inl 2, 416633832437760000000), (Sum.inl 3, 2222047106334720000000), (Sum.inl 26, 2222047106334720000000)]

def reducedTerm315 : Integer.Sparse Master := [(Sum.inl 0, 51144660650926080000), (Sum.inl 1, -21763685383372800000), (Sum.inl 2, 59850134804275200000), (Sum.inl 3, 87054741533491200000)]

def reducedTerm316 : Integer.Sparse Master := [(Sum.inl 0, -117865218032271360000), (Sum.inl 1, 147331522540339200000), (Sum.inl 2, 147331522540339200000)]

def reducedTerm317 : Integer.Sparse Master := [(Sum.inl 0, 434969759518801920000), (Sum.inl 1, -915725809513267200000), (Sum.inl 2, -572328630945792000000), (Sum.inl 3, -1831451619026534400000)]

def reducedTerm318 : Integer.Sparse Master := [(Sum.inl 0, -247002376126464000000), (Sum.inl 1, 247002376126464000000), (Sum.inl 3, 1976019009011712000000), (Sum.inl 26, 1976019009011712000000), (Sum.inl 34, 1976019009011712000000)]

def reducedTerm319 : Integer.Sparse Master := [(Sum.inl 0, -140797528391761920000), (Sum.inl 2, -703987641958809600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def integerMerge0 : Integer.Sparse (Fin 909) := [(0, -12410496), (1, -17962560), (2, 4898880), (5, -9797760), (8, -39191040), (24, 39191040), (27, 29393280), (30, 78382080), (68, 58786560), (126, 78382080), (236, 156764160)]

def integerMerge1 : Integer.Sparse (Fin 909) := [(0, 11104128), (1, -27760320), (2, -4898880), (5, 9797760), (8, -39191040), (24, 39191040), (27, -29393280), (30, 78382080), (68, -58786560), (126, 78382080), (236, 156764160)]

def integerMerge2 : Integer.Sparse (Fin 909) := [(0, -14696640), (1, -11430720), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 58786560), (126, 39191040), (236, 195955200)]

def integerMerge3 : Integer.Sparse (Fin 909) := [(0, -20248704), (1, -6531840), (2, -3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 78382080), (126, 78382080), (236, 235146240)]

def integerMerge4 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -34292160), (2, -8164800), (5, 3265920), (8, -65318400), (24, 39191040), (27, -9797760), (30, 156764160), (68, 19595520), (126, 156764160), (236, 391910400)]

def integerMerge5 : Integer.Sparse (Fin 909) := [(0, -5878656), (1, -544320), (2, 544320), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -13063680), (126, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

def integerMerge6 : Integer.Sparse (Fin 909) := [(0, 8055936), (1, 21228480), (2, -3810240), (5, 3265920), (8, 26127360), (20, -39191040), (24, -13063680), (27, -9797760), (28, -78382080), (30, -26127360), (68, -26127360), (126, -39191040), (208, -117573120), (236, -169827840), (253, -195955200)]

def integerMerge7 : Integer.Sparse (Fin 909) := [(0, -6749568), (1, -2177280), (2, 1088640), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 13063680), (126, 65318400), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerMerge8 : Integer.Sparse (Fin 909) := [(0, 1251936), (1, -3538080), (2, -544320), (3, 8709120), (4, 8709120), (5, 1632960), (8, 13063680), (12, 4354560), (17, -19595520), (20, -39191040), (24, -26127360), (27, -4898880), (30, 6531840), (68, -9797760), (126, -52254720), (203, -39191040), (208, -78382080), (236, -26127360)]

def integerMerge9 : Integer.Sparse (Fin 909) := [(0, -5497632), (1, -5715360), (2, 544320), (3, 8709120), (4, 8709120), (5, -1632960), (12, 4354560), (17, -19595520), (20, -39191040), (24, 13063680), (27, 4898880), (30, 6531840), (68, 3265920), (126, 13063680), (203, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

def integerMerge10 : Integer.Sparse (Fin 909) := [(0, 2558304), (1, 15513120), (2, -3265920), (3, 8709120), (4, 8709120), (5, 1632960), (8, 26127360), (12, 4354560), (17, -19595520), (20, -78382080), (27, -4898880), (28, -78382080), (30, -19595520), (68, -22861440), (126, -26127360), (203, -39191040), (208, -235146240), (236, -235146240), (253, -235146240)]

def integerMerge11 : Integer.Sparse (Fin 909) := [(0, -6586272), (1, -18779040), (2, -11430720), (3, 8709120), (4, 8709120), (5, 4898880), (8, -39191040), (12, 4354560), (17, -19595520), (20, -78382080), (24, 39191040), (27, -14696640), (28, -78382080), (30, 137168640), (68, -3265920), (126, 130636800), (203, -39191040), (208, -235146240), (236, 156764160), (253, -235146240)]

def integerMerge12 : Integer.Sparse (Fin 909) := [(0, -5143824), (1, 3674160), (2, -2993760), (4, 2177280), (31, -6531840), (68, 16329600), (126, 19595520), (207, -19595520), (208, -19595520), (236, 32659200)]

def integerMerge13 : Integer.Sparse (Fin 909) := [(0, -4735584), (1, 2449440), (2, -2721600), (4, 4354560), (31, -13063680), (68, 13063680), (207, -39191040), (208, -39191040), (236, 26127360)]

def integerMerge14 : Integer.Sparse (Fin 909) := [(0, 6477408), (1, -6804000), (2, 3810240), (3, 4354560), (4, 6531840), (31, -6531840), (68, -6531840), (126, -32659200), (203, -19595520), (207, -19595520), (208, -19595520), (236, -19595520), (253, -19595520)]

def integerMerge15 : Integer.Sparse (Fin 909) := [(0, 2993760), (1, -7348320), (2, 3265920), (3, 4354560), (4, 6531840), (31, -6531840), (68, -13063680), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -58786560), (253, -58786560)]

def integerMerge16 : Integer.Sparse (Fin 909) := [(0, -1741824), (1, -4898880), (2, 544320), (3, 4354560), (4, 10886400), (31, -19595520), (126, -45722880), (203, -19595520), (207, -58786560), (208, -97977600), (236, -32659200), (253, -58786560)]

def integerMerge17 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, 4354560), (2, -3810240), (68, 13063680), (126, 26127360), (208, -39191040), (253, -39191040)]

def integerMerge18 : Integer.Sparse (Fin 909) := [(0, -7947072), (1, 2721600), (2, -3265920), (68, 9797760), (126, 13063680), (208, -78382080), (236, -13063680), (253, -39191040)]

def integerMerge19 : Integer.Sparse (Fin 909) := [(0, 1496880), (1, -2857680), (2, 816480), (4, 2177280), (31, -6531840), (68, -6531840), (126, -32659200), (207, -19595520), (208, -58786560), (236, -19595520)]

def integerMerge20 : Integer.Sparse (Fin 909) := [(0, 5742576), (1, -12292560), (2, 4762800), (3, -4354560), (4, 4354560), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (58, 45360), (68, -2177280), (69, -2903040), (126, -13063680), (203, -19595520), (230, 6531840), (236, -13063680), (253, -19595520)]

def integerMerge21 : Integer.Sparse (Fin 909) := [(0, 7239456), (1, -15150240), (2, 5579280), (3, -4354560), (4, 6531840), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -6531840), (58, 45360), (68, -8709120), (69, -2903040), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (230, 6531840), (236, -32659200), (253, -19595520)]

def integerMerge22 : Integer.Sparse (Fin 909) := [(0, -707616), (1, -12428640), (2, 2313360), (3, -4354560), (4, 6531840), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -6531840), (58, 45360), (68, 1088640), (69, -2903040), (126, -32659200), (203, -19595520), (207, -19595520), (208, -137168640), (230, 6531840), (236, -45722880), (253, -58786560)]

def integerMerge23 : Integer.Sparse (Fin 909) := [(0, -2449440), (1, -17327520), (2, 2857680), (4, 17418240), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -26127360), (58, 45360), (68, 1088640), (69, -2903040), (126, -78382080), (203, -39191040), (207, -78382080), (208, -235146240), (230, 6531840), (236, -78382080), (253, -117573120)]

def integerMerge24 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, -36106560), (2, -8573040), (3, 8709120), (4, 26127360), (5, 2721600), (6, -181440), (7, -5806080), (8, -39191040), (12, -1451520), (17, -19595520), (20, -78382080), (23, -8709120), (24, 39191040), (27, -16873920), (28, -78382080), (30, 137168640), (31, -26127360), (58, 45360), (68, -2177280), (69, -2903040), (126, 52254720), (203, -78382080), (207, -78382080), (208, -470292480), (230, 6531840), (236, 78382080), (253, -352719360)]

def integerMerge25 : Integer.Sparse (Fin 909) := [(0, -12410496), (1, -17962560), (2, 4898880), (5, -9797760), (8, -39191040), (24, 39191040), (27, 29393280), (30, 78382080), (68, 58786560), (126, 78382080), (236, 156764160)]

def integerMerge26 : Integer.Sparse (Fin 909) := [(0, 11104128), (1, -27760320), (2, -4898880), (5, 9797760), (8, -39191040), (24, 39191040), (27, -29393280), (30, 78382080), (68, -58786560), (126, 78382080), (236, 156764160)]

def integerMerge27 : Integer.Sparse (Fin 909) := [(0, -14696640), (1, -11430720), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 58786560), (126, 39191040), (236, 195955200)]

def integerMerge28 : Integer.Sparse (Fin 909) := [(0, -20248704), (1, -6531840), (2, -3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 78382080), (126, 78382080), (236, 235146240)]

def integerMerge29 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -34292160), (2, -8164800), (5, 3265920), (8, -65318400), (24, 39191040), (27, -9797760), (30, 156764160), (68, 19595520), (126, 156764160), (236, 391910400)]

def integerMerge30 : Integer.Sparse (Fin 909) := [(0, -5878656), (1, -544320), (2, 544320), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -13063680), (126, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

def integerMerge31 : Integer.Sparse (Fin 909) := [(0, 8055936), (1, 21228480), (2, -3810240), (5, 3265920), (8, 26127360), (20, -39191040), (24, -13063680), (27, -9797760), (28, -78382080), (30, -26127360), (68, -26127360), (126, -39191040), (208, -117573120), (236, -169827840), (253, -195955200)]

def integerMerge32 : Integer.Sparse (Fin 909) := [(0, -6749568), (1, -2177280), (2, 1088640), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 13063680), (126, 65318400), (208, -39191040), (236, -39191040), (253, -39191040)]

def integerMerge33 : Integer.Sparse (Fin 909) := [(0, 1251936), (1, -3538080), (2, -544320), (3, 8709120), (4, 8709120), (5, 1632960), (8, 13063680), (12, 4354560), (17, -19595520), (20, -39191040), (24, -26127360), (27, -4898880), (30, 6531840), (68, -9797760), (126, -52254720), (203, -39191040), (208, -78382080), (236, -26127360)]

def integerMerge34 : Integer.Sparse (Fin 909) := [(0, -5497632), (1, -5715360), (2, 544320), (3, 8709120), (4, 8709120), (5, -1632960), (12, 4354560), (17, -19595520), (20, -39191040), (24, 13063680), (27, 4898880), (30, 6531840), (68, 3265920), (126, 13063680), (203, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

def integerMerge35 : Integer.Sparse (Fin 909) := [(0, 2558304), (1, 15513120), (2, -3265920), (3, 8709120), (4, 8709120), (5, 1632960), (8, 26127360), (12, 4354560), (17, -19595520), (20, -78382080), (27, -4898880), (28, -78382080), (30, -19595520), (68, -22861440), (126, -26127360), (203, -39191040), (208, -235146240), (236, -235146240), (253, -235146240)]

def integerMerge36 : Integer.Sparse (Fin 909) := [(0, -6586272), (1, -18779040), (2, -11430720), (3, 8709120), (4, 8709120), (5, 4898880), (8, -39191040), (12, 4354560), (17, -19595520), (20, -78382080), (24, 39191040), (27, -14696640), (28, -78382080), (30, 137168640), (68, -3265920), (126, 130636800), (203, -39191040), (208, -235146240), (236, 156764160), (253, -235146240)]

def integerMerge37 : Integer.Sparse (Fin 909) := [(0, -5143824), (1, 3674160), (2, -2993760), (4, 2177280), (31, -6531840), (68, 16329600), (126, 19595520), (207, -19595520), (208, -19595520), (236, 32659200)]

def integerMerge38 : Integer.Sparse (Fin 909) := [(0, -4735584), (1, 2449440), (2, -2721600), (4, 4354560), (31, -13063680), (68, 13063680), (207, -39191040), (208, -39191040), (236, 26127360)]

def integerMerge39 : Integer.Sparse (Fin 909) := [(0, 6477408), (1, -6804000), (2, 3810240), (3, 4354560), (4, 6531840), (31, -6531840), (68, -6531840), (126, -32659200), (203, -19595520), (207, -19595520), (208, -19595520), (236, -19595520), (253, -19595520)]

def integerMerge40 : Integer.Sparse (Fin 909) := [(0, 2993760), (1, -7348320), (2, 3265920), (3, 4354560), (4, 6531840), (31, -6531840), (68, -13063680), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -58786560), (253, -58786560)]

def integerMerge41 : Integer.Sparse (Fin 909) := [(0, -1741824), (1, -4898880), (2, 544320), (3, 4354560), (4, 10886400), (31, -19595520), (126, -45722880), (203, -19595520), (207, -58786560), (208, -97977600), (236, -32659200), (253, -58786560)]

def integerMerge42 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, 4354560), (2, -3810240), (68, 13063680), (126, 26127360), (208, -39191040), (253, -39191040)]

def integerMerge43 : Integer.Sparse (Fin 909) := [(0, -7947072), (1, 2721600), (2, -3265920), (68, 9797760), (126, 13063680), (208, -78382080), (236, -13063680), (253, -39191040)]

def integerMerge44 : Integer.Sparse (Fin 909) := [(0, 1496880), (1, -2857680), (2, 816480), (4, 2177280), (31, -6531840), (68, -6531840), (126, -32659200), (207, -19595520), (208, -58786560), (236, -19595520)]

def integerMerge45 : Integer.Sparse (Fin 909) := [(0, 6051024), (1, -11385360), (2, 4082400), (3, 4354560), (4, 4354560), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (35, -5806080), (63, -8709120), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

def integerMerge46 : Integer.Sparse (Fin 909) := [(0, 7547904), (1, -14243040), (2, 4898880), (3, 4354560), (4, 6531840), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -6531840), (35, -5806080), (63, -8709120), (68, -9797760), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -32659200), (253, -19595520)]

def integerMerge47 : Integer.Sparse (Fin 909) := [(0, -399168), (1, -11521440), (2, 1632960), (3, 4354560), (4, 6531840), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -6531840), (35, -5806080), (63, -8709120), (126, -32659200), (203, -19595520), (207, -19595520), (208, -137168640), (236, -45722880), (253, -58786560)]

def integerMerge48 : Integer.Sparse (Fin 909) := [(0, -2140992), (1, -16420320), (2, 2177280), (3, 8709120), (4, 17418240), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -26127360), (35, -5806080), (63, -8709120), (126, -78382080), (203, -39191040), (207, -78382080), (208, -235146240), (236, -78382080), (253, -117573120)]

def integerMerge49 : Integer.Sparse (Fin 909) := [(0, -8727264), (1, -35199360), (2, -9253440), (3, 17418240), (4, 26127360), (5, 4536000), (6, 272160), (7, -8709120), (8, -39191040), (12, -4354560), (13, -5806080), (17, -19595520), (20, -78382080), (23, -13063680), (24, 39191040), (27, -13608000), (28, -78382080), (30, 137168640), (31, -26127360), (35, -5806080), (63, -8709120), (68, -3265920), (126, 52254720), (203, -78382080), (207, -78382080), (208, -470292480), (236, 78382080), (253, -352719360)]

end MUB6.Certificate.PairTargetSemantics

end OAI
end


