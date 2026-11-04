-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
-- name    : Submission_ThreeSum_LightBandPrimeStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:00:47.494475+00:00
-- url     : https://prove2.me/theorems/968f89da-8af1-475f-b71d-c07b8d76acec
-- title:
--   Light Band Prime Stage
-- statement:
--   Definitions and structural lemmas for Light Band Prime Stage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeStage.lean

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
namespace ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def finiteMass (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.finiteAllProducts nA nB nC (bandSize n) rs)
    (fun t => C t.2.2.val-B t.2.1.val-BandRawA.valueAt nA (bandSize n) rs A t.1.val)
    (Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
      (LightPrimePool.size (primeWindow n)))) q
abbrev program := LightBandPrimeSetup.program
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c n nA nB nC k recs free : ℕ}
end ThreeSum.LightBandPrimeStage


