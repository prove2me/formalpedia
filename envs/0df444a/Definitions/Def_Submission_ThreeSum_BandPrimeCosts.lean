-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPrimeCosts
-- name    : Submission_ThreeSum_BandPrimeCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:48:14.287757+00:00
-- url     : https://prove2.me/theorems/ffa64e73-e75b-4d41-afa8-3f4250783660
-- title:
--   Band Prime Costs
-- statement:
--   Definitions and structural lemmas for Band Prime Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
set_option autoImplicit false
namespace ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def unit (p g U : ℕ) : ℕ :=
  LightModuloCounts.time p g g g U+LightWeightedScore.jointTime p+1000
def core (p g R s U : ℕ) : ℕ := (R+1)*(s+1)^2*unit p g U
def timeBudget (k n : ℕ) : ℕ := LightPrimePool.time (primeWindow n)+
  15*(primeDepth radix n+1)*(3*bandCount n^2+1)*
    (LightPrimePool.size (primeWindow n)+1)^2*perTripleBudget k n
end ThreeSum.BandPrimeCosts


