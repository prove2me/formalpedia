-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
-- name    : Submission_Weighted_Global_TernarySignedFeatureHash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:35:45.755732+00:00
-- url     : https://prove2.me/theorems/a8209601-6390-4086-9462-75585cf99c38
-- title:
--   Ternary Signed Feature Hash
-- statement:
--   Definitions and structural lemmas for Ternary Signed Feature Hash, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]
def unfeature (J : ℕ) : (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Coordinate J→ZMod p) where
  toFun v := Sum.elim (fun j => v ⟨j.val,by omega⟩)
    (fun t => if t then v ⟨J+1,by omega⟩ else v ⟨J,by omega⟩)
  map_add' v w := by funext k; cases k with
    | inl j => rfl
    | inr t => cases t <;> rfl
  map_smul' c v := by funext k; cases k with
    | inl j => rfl
    | inr t => cases t <;> rfl
def hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) :
    (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p) := H.comp (unfeature J)
end ThreeSum.WeightedGlobalSignedFeatureHash


