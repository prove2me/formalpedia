-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:39:13.927726+00:00
-- url     : https://prove2.me/theorems/c8cdde04-ee43-49a1-97f1-22d9d179466a
-- title:
--   TernarySignedFeatureHash
-- statement:
--   Definitions and structural lemmas for TernarySignedFeatureHash, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedFeatureHash.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


