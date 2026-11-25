-- Prove2me | solution 1 for Arxiv1510_02920.im_perm_limits
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:00:26.192576+00:00
-- url     : https://prove2.me/submissions/238a55a4-be89-49dd-be67-5ff36a977cf5

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

theorem im_perm_limits (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    Tendsto (fun ω : ℝ => ω * (perm c (ansatzP f γ) x (ω : ℂ)).im) (𝓝[≠] 0)
        (𝓝 (-c * deriv f x / γ ^ 2)) ∧
      Tendsto (fun ω : ℝ => ω ^ 3 * (perm c (ansatzP f γ) x (ω : ℂ)).im) atTop
        (𝓝 (4 * γ * f x + c * deriv f x)) := by
  set F := f x with hFx
  set D := deriv f x with hDx
  have hγ2 : 0 < γ ^ 2 := by positivity
  constructor
  · set g : ℝ → ℝ := fun ω => (4 * γ * ω ^ 2 * F * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * F) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * D) / ((γ ^ 2 + ω ^ 2) ^ 4) with hg
    have hgc : ContinuousAt g 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      positivity
    have hg0 : g 0 = -c * D / γ ^ 2 := by
      simp only [hg]; field_simp; ring
    rw [← hg0]
    refine (hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
    rw [im_perm_formula c hc γ hγ f hf x ω hω, hg]
    try rw [← hFx]
    try rw [← hDx]
    have : 0 < γ ^ 2 + ω ^ 2 := by positivity
    field_simp
    try ring
  · set G : ℝ → ℝ := fun t => (4 * γ * F * (γ ^ 2 * t ^ 2 + 1) ^ 2 + 4 * γ * F ^ 2 * (γ ^ 2 * t ^ 4 - t ^ 2) -
        c * D * (γ ^ 2 * t ^ 2 - 1) * (γ ^ 2 * t ^ 2 + 1) ^ 2) / (γ ^ 2 * t ^ 2 + 1) ^ 4 with hG
    have hGc : ContinuousAt G 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      positivity
    have hG0 : G 0 = 4 * γ * F + c * D := by simp only [hG]; ring
    rw [← hG0]
    refine (hGc.tendsto.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
    rw [Function.comp_apply, im_perm_formula c hc γ hγ f hf x ω hω.ne', hG]
    have : 0 < γ ^ 2 + ω ^ 2 := by positivity
    field_simp
    ring

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    Tendsto (fun ω : ℝ => ω * (perm c (ansatzP f γ) x (ω : ℂ)).im) (𝓝[≠] 0)
        (𝓝 (-c * deriv f x / γ ^ 2)) ∧
      Tendsto (fun ω : ℝ => ω ^ 3 * (perm c (ansatzP f γ) x (ω : ℂ)).im) atTop
        (𝓝 (4 * γ * f x + c * deriv f x)) :=
  im_perm_limits c hc γ hγ f hf x
