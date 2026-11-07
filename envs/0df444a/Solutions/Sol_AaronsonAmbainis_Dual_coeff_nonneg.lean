-- Prove2me | solution 1 for AaronsonAmbainis.Dual.coeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:32.001197+00:00
-- url     : https://prove2.me/submissions/a8de566a-c492-423f-8b26-7cc7c778210f

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Functional

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]
omit [Fintype β]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (φ : (β → ℝ) →L[ℝ] ℝ) (r : ℝ)
    (h : ∀ v : β → ℝ, (∀ b, 0 ≤ v b) → r < φ v) (b : β) :
    0 ≤ φ (Pi.single b 1) := by
  by_contra hneg
  rw [not_le] at hneg
  -- `v = 0` gives `r < 0`
  have hr : r < 0 := by
    have h0 := h 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- `v = (r / φ e_b) • e_b` lies in the orthant and has `φ v = r`
  have hx := h ((r / φ (Pi.single b 1)) • (Pi.single b (1 : ℝ) : β → ℝ)) (fun c => by
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_nonneg (div_nonneg_of_nonpos hr.le hneg.le) ?_
    rw [Pi.single_apply]
    split_ifs <;> norm_num)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at hx
  exact lt_irrefl _ hx
end AaronsonAmbainis.Dual
