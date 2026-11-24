-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:46.270365+00:00
-- url     : https://prove2.me/theorems/8706a001-daa5-488d-8795-f7a8705abfaf
-- title:
--   PHilbert Prime
-- statement:
--   Definitions and structural lemmas for PHilbert Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section Walk
variable {K : Type*} [Fintype K] [DecidableEq K]
end Walk
section Multilinear
variable {K : Type*} [Fintype K] [DecidableEq K]
end Multilinear
section Expansion
variable {K : Type*} [Fintype K] [DecidableEq K]
def ofPositionAdditive {n : ℕ} (L : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      L (Function.update bs j (x + y)) = L (Function.update bs j x) + L (Function.update bs j y)) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := L
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun y => L (Function.update m i y)) (hadd m i)
    exact φ.map_zsmul c x
end Expansion
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


