-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayInitial
-- name    : GrothendieckLB_Supplement_cqReplayInitial
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:45:38.939854+00:00
-- url     : https://prove2.me/theorems/a7335d80-0150-4684-bc3b-8d0b582c1382
-- title:
--   Initial row checks for the cubic–quintic integer replay
-- statement:
--   The initial checks match both rows of the first checkpoint, the six raw moment seeds, the zeroth Gaussian weight row and the zeroth polynomial power.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayRows
import Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def initialChecks : Bool :=
  decide ((checkpoint 0).1=startData ∧ (checkpoint 0).2=startData) &&
  (List.range 6).all (fun b => decide (raw b=entry zeroCombination (momentRows 0) b)) &&
  (List.range 252).all fun b => decide (weight 0 b=zeroWeightAt b ∧ power 0 b=(if b=0 then fixed coefficientScale else zeroInterval))

end GrothendieckLB.Supplement.CQHeadCertificate


