-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
-- name    : Submission_Weighted_Global_TernaryArenaPostSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:29:34.818039+00:00
-- url     : https://prove2.me/theorems/6de6387d-5e3d-4cde-b49e-afe493e07a14
-- title:
--   Ternary Arena Post Selection
-- statement:
--   Definitions and structural lemmas for Ternary Arena Post Selection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
def compactInput (I : Input) (keysB keysC : ℕ→ℕ) : Input :=
  { I with nB:=(indices keysB I.nB).length, nC:=(indices keysC I.nC).length }
def selectedInput (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) : Input :=
  WeightedGlobalArenaNativeComplete.input (compactInput I keysB keysC) U radix nA H A
    (compact keysB B I.nB) (compact keysC C I.nC)
end ThreeSum.WeightedGlobalArenaPostSelection


