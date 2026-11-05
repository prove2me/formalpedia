-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:16:26.209294+00:00
-- url     : https://prove2.me/theorems/a6c0509e-9d65-4a23-9e49-0c6505cfecc8
-- title:
--   LightTernaryCertifiedMomentDriver
-- statement:
--   Definitions and structural lemmas for LightTernaryCertifiedMomentDriver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryCertifiedMomentDriver.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentDriver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentChannelFactory
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


