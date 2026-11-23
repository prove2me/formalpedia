-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:07.501117+00:00
-- url     : https://prove2.me/theorems/4478dc2f-14f2-48a8-bc89-2fe0bbc052b9
-- title:
--   Gap Statement
-- statement:
--   Definitions and structural lemmas for Gap Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_eq
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_neg_left
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
namespace SemicharacterExponentialLemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end SemicharacterExponentialLemmas
open SemicharacterExponentialLemmas
namespace IsQuadFn0
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
theorem b_eq (h : IsQuadFn0 φ b) (x y : M) : b x y = φ (x + y) / (φ x * φ y) := by
  rw [h.1 x y, eq_div_iff (mul_ne_zero (h.4 x) (h.4 y))]
  ring
theorem b_zero_left (h : IsQuadFn0 φ b) (y : M) : b 0 y = 1 := by
  have h0 : φ 0 = 1 := by simpa using h.3 0 y
  rw [h.b_eq, zero_add, h0, one_mul, div_self (h.4 y)]
theorem b_neg_left (h : IsQuadFn0 φ b) (x y : M) : b (-x) y = (b x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← h.2]
  simp [h.b_zero_left]
def rad (h : IsQuadFn0 φ b) : AddSubgroup M where
  carrier := {x | ∀ y, b x y = 1}
  zero_mem' := h.b_zero_left
  add_mem' := by
    intro x x' hx hx' y
    rw [h.left, hx y, hx' y, mul_one]
  neg_mem' := by
    intro x hx y
    rw [h.b_neg_left, hx y, inv_one]
end IsQuadFn0
end Formalism.L2.Th1.H


