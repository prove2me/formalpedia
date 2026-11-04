-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
-- name    : Submission_Weighted_Global_LightTernaryControllerFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:29:30.377668+00:00
-- url     : https://prove2.me/theorems/11c4e5d9-1815-44cf-a909-b8f4c79d5d64
-- title:
--   Light Ternary Controller Full
-- statement:
--   Definitions and structural lemmas for Light Ternary Controller Full, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFull.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFull
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
set_option autoImplicit false
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


