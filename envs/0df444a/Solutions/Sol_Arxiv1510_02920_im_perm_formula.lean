-- Prove2me | solution 1 for Arxiv1510_02920.im_perm_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:59:29.601048+00:00
-- url     : https://prove2.me/submissions/3bf0e48d-1062-4342-aabc-b568fd5e97cf

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem im_perm_formula (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x ω : ℝ) (hω : ω ≠ 0) :
    (perm c (ansatzP f γ) x (ω : ℂ)).im =
      (4 * γ * ω ^ 2 * f x * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * f x) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * deriv f x) /
        (ω * (γ ^ 2 + ω ^ 2) ^ 4) := by
  set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
  have hd : HasDerivAt (fun y : ℝ => ansatzP f γ y (ω : ℂ)) (((deriv f x : ℝ) : ℂ) / Z) x := by
    have := (((hf x).hasDerivAt.ofReal_comp).div_const Z).const_add 1
    exact this
  unfold perm
  rw [hd.deriv]
  unfold ansatzP
  rw [← hZ]
  have hZe : Z = ((γ ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((-2 * γ * ω : ℝ) : ℂ) * Complex.I := by
    rw [hZ]; apply Complex.ext <;> simp [sq] <;> ring
  have hD : 0 < γ ^ 2 + ω ^ 2 := by positivity
  have hZinv : Z⁻¹ = (((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2 : ℝ) : ℂ) +
      ((2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [hZe]
    apply inv_eq_of_mul_eq_one_right
    have key1 : (γ ^ 2 - ω ^ 2) * ((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2) -
        (-2 * γ * ω) * (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) = 1 := by field_simp; ring
    have key2 : (γ ^ 2 - ω ^ 2) * (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) +
        (-2 * γ * ω) * ((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2) = 0 := by ring
    generalize (γ ^ 2 - ω ^ 2) = p at key1 key2 ⊢
    generalize (-2 * γ * ω) = r at key1 key2 ⊢
    generalize (p / (γ ^ 2 + ω ^ 2) ^ 2) = A at key1 key2 ⊢
    generalize (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) = B at key1 key2 ⊢
    apply Complex.ext <;> simp <;> linarith
  simp only [div_eq_mul_inv _ Z, hZinv]
  simp only [sq, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.div_re, Complex.div_im, Complex.normSq_ofReal, Complex.inv_re, Complex.inv_im]
  field_simp
  ring

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x ω : ℝ) (hω : ω ≠ 0) :
    (perm c (ansatzP f γ) x (ω : ℂ)).im =
      (4 * γ * ω ^ 2 * f x * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * f x) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * deriv f x) /
        (ω * (γ ^ 2 + ω ^ 2) ^ 4) :=
  im_perm_formula c hc γ hγ f hf x ω hω
