-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFull
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:38:27.551183+00:00
-- url     : https://prove2.me/theorems/84261ee8-df40-41f3-ad95-dcfe1c626c66
-- title:
--   LightTernaryControllerFull
-- statement:
--   Definitions and structural lemmas for LightTernaryControllerFull, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFull.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFull
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
structure Candidate.FullGuard {C : Config} [Fact C.p.Prime] (D : Candidate C) (lim : Limits)
    (depth K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) : Prop where
  toGuard : D.Guard lim depth K R S raws words maps μ
  retain : C.wanted+(D.data.wantedRows R S raws words maps).length≤C.tensor
  locations : ∀x∈[C.flags+C.seed,C.scoreB+C.seed,C.scoreC+C.seed,C.scorePaired+C.seed],
    x<C.Bnew ∧ x≠C.header+104
def Candidate.FullDone {C : Config} [Fact C.p.Prime] (D : Candidate C)
    (K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ ν : ℕ→ℤ) : Prop :=
  D.Done K μ ν ∧ LightWeightedGlobalSeedScoreFull.Outputs C D.data R S raws words maps ν
end ThreeSum.LightWeightedGlobalControllerFactory
end
end WeightedCache3SUMRefinement_e1ae71d


