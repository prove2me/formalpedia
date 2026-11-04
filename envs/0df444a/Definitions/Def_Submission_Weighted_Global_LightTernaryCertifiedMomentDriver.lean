-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
-- name    : Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:52:27.274196+00:00
-- url     : https://prove2.me/theorems/b8a69920-3a15-4148-a002-4d4187ba63f1
-- title:
--   Light Ternary Certified Moment Driver
-- statement:
--   Definitions and structural lemmas for Light Ternary Certified Moment Driver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryCertifiedMomentDriver.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentDriver
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalCertifiedMomentDriver
open Light TernaryMomentSchedule LightWeightedGlobalMomentChannelFactory
set_option maxHeartbeats 3000000
def cost {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (c : ℕ×ℕ) : ℕ :=
  LightTernaryMomentChannelStep.time c.1 c.2 S.left.NL S.right.NL S.front.count S.runtime 106
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (terms : ℕ) : Program :=
  LightWeightedGlobalMomentDriver.program S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs
    (channels terms) terms (9+S.argv.length)
def time {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (terms : ℕ) : ℕ :=
  LightWeightedGlobalMomentDriver.time (channels terms) (cost S) terms S.front.count (9+S.argv.length)
end ThreeSum.LightWeightedGlobalCertifiedMomentDriver


