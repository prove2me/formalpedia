-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPrepare
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPrepare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:08:04.43798+00:00
-- url     : https://prove2.me/theorems/3c0b35bd-5358-4ea5-9c15-214862b28f8a
-- title:
--   FrozenPrepare
-- statement:
--   Definitions and structural lemmas for FrozenPrepare, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenPrepare.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenBranches
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
def prepTime (N : ℕ) : ℕ :=
  LightTernaryCodes.digitTime (2*N)+LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+300
end ThreeSum.LightWeightedFrozenQuery
end WeightedCache3SUMRefinement_e1ae71d


