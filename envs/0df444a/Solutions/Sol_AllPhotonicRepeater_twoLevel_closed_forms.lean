-- Prove2me | solution 1 for AllPhotonicRepeater.twoLevel_closed_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:43:25.763734+00:00
-- url     : https://prove2.me/submissions/e132963a-2c05-44d5-8e5c-1ad0e9a65555

import Mathlib
import Definitions.Def_AllPhotonicRepeater_treeSize
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess

set_option autoImplicit false

namespace Aux_APR2L
open AllPhotonicRepeater

theorem z2 (ε0 : ℝ) (b : ℕ → ℕ) : indirectZSuccess ε0 1 b 2 = 0 := by
  rw [indirectZSuccess]
  simp

theorem z3 (ε0 : ℝ) (b : ℕ → ℕ) : indirectZSuccess ε0 1 b 3 = 0 := by
  rw [indirectZSuccess]
  simp

theorem z1 (ε0 : ℝ) (b : ℕ → ℕ) : indirectZSuccess ε0 1 b 1 = 1 - ε0 ^ b 1 := by
  rw [indirectZSuccess]
  simp

theorem z0 (ε0 : ℝ) (b : ℕ → ℕ) :
    indirectZSuccess ε0 1 b 0 = 1 - (1 - (1 - ε0) ^ (b 1 + 1)) ^ b 0 := by
  rw [indirectZSuccess]
  simp only [zero_le, dite_true, zero_add, le_refl, ite_true, z2, mul_zero, add_zero]
  rw [pow_succ]
  ring

end Aux_APR2L

open AllPhotonicRepeater Aux_APR2L in
theorem solution (ε0 : ℝ) (b : ℕ → ℕ) :
    indirectZSuccess ε0 1 b 1 = 1 - ε0 ^ b 1 ∧
    xSuccess ε0 1 b = 1 - (1 - (1 - ε0) ^ (b 1 + 1)) ^ b 0 ∧
    zSuccess ε0 1 b = (1 - ε0 ^ (b 1 + 1)) ^ b 0 ∧
    treeSize 1 b = b 0 + b 0 * b 1 := by
  refine ⟨z1 ε0 b, ?_, ?_, ?_⟩
  · unfold xSuccess; exact z0 ε0 b
  · unfold zSuccess; rw [z1]; congr 1; ring
  · unfold treeSize
    simp [Finset.sum_range_succ, Finset.prod_range_succ]
