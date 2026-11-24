-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
-- name    : Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:45.577801+00:00
-- url     : https://prove2.me/theorems/3041b4b4-4392-494a-b9d1-9b01b1fdd0e1
-- title:
--   Exists Refl
-- statement:
--   Definitions and structural lemmas for Exists Refl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/ExistsRefl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {n : Type} [Fintype n] [DecidableEq n]
noncomputable def hf (M : Matrix n n ℂ) : (n → ℂ) →ₗ[ℂ] (n → ℂ) →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x ⬝ᵥ M *ᵥ star y)
    (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => by rw [star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [star_smul, mulVec_smul, dotProduct_smul]; rfl)
variable {M θ : Matrix n n ℂ}
end PositivityTheory.ThKG.Tow.Levi


