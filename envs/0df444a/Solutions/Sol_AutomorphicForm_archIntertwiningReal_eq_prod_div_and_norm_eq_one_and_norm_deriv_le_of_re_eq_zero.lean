-- Prove2me | solution 1 for AutomorphicForm.archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fbaeea97-6585-5cb7-824f-3d3a2892c355

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero

set_option autoImplicit false

namespace Ws31
namespace AxisR

open Complex Finset
open scoped ComplexConjugate

theorem a_re_pos (ε i : ℕ) : (1 : ℝ) ≤ (((1 + ε + 2 * i : ℕ)) : ℝ) := by
  push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i), (Nat.cast_nonneg ε : (0:ℝ) ≤ ε)]

theorem GammaR_mul_inv_GammaR_add (z : ℂ) (hz : 0 < z.re) (j : ℕ) :
    Complex.Gammaℝ z * (Complex.Gammaℝ (z + 2 * (j : ℂ)))⁻¹ =
      (2 * (Real.pi : ℂ)) ^ j / ∏ i ∈ Finset.range j, (z + 2 * (i : ℂ)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hGne : ∀ n : ℕ, Complex.Gammaℝ (z + 2 * (n : ℂ)) ≠ 0 := by
    intro n
    rw [Ne, Complex.Gammaℝ_eq_zero_iff, not_exists]; intro l hl
    have := congrArg Complex.re hl; simp at this
    have : (0:ℝ) ≤ l := Nat.cast_nonneg l; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hzne : ∀ n : ℕ, z + 2 * (n : ℂ) ≠ 0 := by
    intro n h; have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  induction j with
  | zero =>
    have h0 := hGne 0
    simp only [Nat.cast_zero, mul_zero, add_zero] at h0
    simp [mul_inv_cancel₀ h0]
  | succ j ih =>
    have hstep : Complex.Gammaℝ (z + 2 * ((j + 1 : ℕ) : ℂ)) =
        Complex.Gammaℝ (z + 2 * (j : ℂ)) * (z + 2 * (j : ℂ)) / 2 / Real.pi := by
      rw [show z + 2 * ((j + 1 : ℕ) : ℂ) = (z + 2 * (j : ℂ)) + 2 by push_cast; ring]
      exact Complex.Gammaℝ_add_two (hzne j)
    have hP : ∏ i ∈ Finset.range j, (z + 2 * (i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hzne i
    rw [hstep, Finset.prod_range_succ, pow_succ]
    rw [show Complex.Gammaℝ z * (Complex.Gammaℝ (z + 2 * (j : ℂ)) * (z + 2 * (j : ℂ)) / 2 / (Real.pi : ℂ))⁻¹
      = (Complex.Gammaℝ z * (Complex.Gammaℝ (z + 2 * (j : ℂ)))⁻¹) * (2 * (Real.pi : ℂ) / (z + 2 * (j : ℂ))) by
        field_simp, ih]
    field_simp

theorem prod_halfStep (w : ℂ) (ε j : ℕ) :
    ∏ i ∈ Finset.range j, ((w + 1 - (ε : ℂ)) / 2 - 1 - (i : ℂ)) =
      (∏ i ∈ Finset.range j, (w - ((1 + ε + 2 * i : ℕ) : ℂ))) / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h2 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    push_cast
    ring

theorem rational_form (k : ℤ) (ε j : ℕ) (w : ℂ) (hw : -1 < w.re) :
    (-Complex.I) ^ k *
        ((∏ i ∈ Finset.range j, ((w + 1 - (ε : ℂ)) / 2 - 1 - (i : ℂ))) / (Real.pi : ℂ) ^ j) *
        Complex.Gammaℝ (w + 1 + (ε : ℂ)) * (Complex.Gammaℝ (w + 1 + ((ε + 2 * j : ℕ) : ℂ)))⁻¹
      = (-Complex.I) ^ k *
        ∏ i ∈ Finset.range j, ((w - ((1 + ε + 2 * i : ℕ) : ℂ)) / (w + ((1 + ε + 2 * i : ℕ) : ℂ))) := by
  have hz : 0 < (w + 1 + (ε : ℂ)).re := by simp; have : (0:ℝ) ≤ ε := Nat.cast_nonneg ε; linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hshift : w + 1 + ((ε + 2 * j : ℕ) : ℂ) = (w + 1 + (ε : ℂ)) + 2 * (j : ℂ) := by push_cast; ring
  rw [hshift, mul_assoc, GammaR_mul_inv_GammaR_add _ hz j, prod_halfStep, Finset.prod_div_distrib]
  have hden : ∏ i ∈ Finset.range j, (w + 1 + (ε : ℂ) + 2 * (i : ℂ)) = ∏ i ∈ Finset.range j, (w + ((1 + ε + 2 * i : ℕ) : ℂ)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [hden, mul_pow]
  have h2 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
  have hπj : (Real.pi : ℂ) ^ j ≠ 0 := pow_ne_zero _ hπ
  have hD : ∏ i ∈ Finset.range j, (w + ((1 + ε + 2 * i : ℕ) : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _ h
    have := congrArg Complex.re h; simp at this
    have : (0:ℝ) ≤ i := Nat.cast_nonneg i; have : (0:ℝ) ≤ ε := Nat.cast_nonneg ε; linarith
  field_simp

theorem norm_blaschke_eq_one (w : ℂ) (hw : w.re = 0) (a : ℕ) (ha : (1 : ℝ) ≤ a) :
    ‖(w - (a : ℂ)) / (w + (a : ℂ))‖ = 1 := by
  have hconj : w + (a : ℂ) = -(conj (w - (a : ℂ))) := by
    apply Complex.ext <;> simp [hw]
  have hne : w + (a : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; simp [this] at ha; exact absurd ha (by norm_num)
  rw [norm_div, hconj, norm_neg, Complex.norm_conj, div_self]
  rw [norm_ne_zero_iff]
  intro h0
  apply hne
  rw [hconj, h0, map_zero, neg_zero]

theorem hasDerivAt_blaschke (w : ℂ) (hw : w.re = 0) (a : ℕ) (ha : (1 : ℝ) ≤ a) :
    HasDerivAt (fun z : ℂ => (z - (a : ℂ)) / (z + (a : ℂ))) (2 * (a : ℂ) / (w + (a : ℂ)) ^ 2) w ∧
      ‖2 * (a : ℂ) / (w + (a : ℂ)) ^ 2‖ ≤ 2 := by
  have hne : w + (a : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; simp [this] at ha; exact absurd ha (by norm_num)
  constructor
  · have h := ((hasDerivAt_id w).sub_const (a : ℂ)).div ((hasDerivAt_id w).add_const (a : ℂ)) hne
    convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp; ring1) | (simp only [id_eq]; ring1)
  · have hwa : (a : ℝ) ≤ ‖w + (a : ℂ)‖ := by
      have := Complex.abs_re_le_norm (w + (a : ℂ))
      simp [hw] at this
      exact this
    have ha0 : (0 : ℝ) < a := by linarith
    rw [norm_div, norm_pow, norm_mul, Complex.norm_two, Complex.norm_natCast, div_le_iff₀ (by positivity)]
    nlinarith [hwa, ha]

theorem main (k : ℤ) (ε j : ℕ) :
    let N : ℂ → ℂ := fun w => (-Complex.I) ^ k *
        ((∏ i ∈ Finset.range j, ((w + 1 - (ε : ℂ)) / 2 - 1 - (i : ℂ))) / (Real.pi : ℂ) ^ j) *
        Complex.Gammaℝ (w + 1 + (ε : ℂ)) * (Complex.Gammaℝ (w + 1 + ((ε + 2 * j : ℕ) : ℂ)))⁻¹
    (∀ w : ℂ, -1 < w.re → N w = (-Complex.I) ^ k *
        ∏ i ∈ Finset.range j, ((w - ((1 + ε + 2 * i : ℕ) : ℂ)) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)))) ∧
    (∀ w : ℂ, w.re = 0 → ‖N w‖ = 1 ∧ DifferentiableAt ℂ N w ∧ ‖deriv N w‖ ≤ 2 * j) := by
  intro N
  have hrat : ∀ w : ℂ, -1 < w.re → N w = (-Complex.I) ^ k *
      ∏ i ∈ Finset.range j, ((w - ((1 + ε + 2 * i : ℕ) : ℂ)) / (w + ((1 + ε + 2 * i : ℕ) : ℂ))) :=
    fun w hw => rational_form k ε j w hw
  refine ⟨hrat, fun w hw => ?_⟩

  set R : ℂ → ℂ := fun z => (-Complex.I) ^ k *
      ∏ i ∈ Finset.range j, ((z - ((1 + ε + 2 * i : ℕ) : ℂ)) / (z + ((1 + ε + 2 * i : ℕ) : ℂ))) with hR
  have hev : N =ᶠ[nhds w] R := by
    have hopen : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z : ℂ | -1 < z.re}, hopen.mem_nhds (by simp [hw]), fun z hz => ?_⟩
    exact hrat z hz
  have hIk : ‖(-Complex.I) ^ k‖ = 1 := by rw [norm_zpow, norm_neg, Complex.norm_I, one_zpow]

  have hf : ∀ i ∈ Finset.range j, HasDerivAt (fun z : ℂ => (z - ((1 + ε + 2 * i : ℕ) : ℂ)) / (z + ((1 + ε + 2 * i : ℕ) : ℂ)))
      (2 * ((1 + ε + 2 * i : ℕ) : ℂ) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)) ^ 2) w :=
    fun i _ => (hasDerivAt_blaschke w hw _ (a_re_pos ε i)).1
  have hP := HasDerivAt.finsetProd hf
  have hRd : HasDerivAt R ((-Complex.I) ^ k * ∑ i ∈ Finset.range j,
      (∏ l ∈ (Finset.range j).erase i, ((w - ((1 + ε + 2 * l : ℕ) : ℂ)) / (w + ((1 + ε + 2 * l : ℕ) : ℂ)))) •
        (2 * ((1 + ε + 2 * i : ℕ) : ℂ) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)) ^ 2)) w := by
    have := hP.const_mul ((-Complex.I) ^ k)
    convert this using 2
    · rfl
    · rfl
    simp only [hR, Finset.prod_apply]
  have hNd : HasDerivAt N _ w := hRd.congr_of_eventuallyEq hev
  refine ⟨?_, hNd.differentiableAt, ?_⟩
  · rw [hev.eq_of_nhds, hR, norm_mul, hIk, one_mul, norm_prod]
    exact Finset.prod_eq_one fun i _ => norm_blaschke_eq_one w hw _ (a_re_pos ε i)
  · rw [hNd.deriv, norm_mul, hIk, one_mul]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range j,
        ‖(∏ l ∈ (Finset.range j).erase i, ((w - ((1 + ε + 2 * l : ℕ) : ℂ)) / (w + ((1 + ε + 2 * l : ℕ) : ℂ)))) •
          (2 * ((1 + ε + 2 * i : ℕ) : ℂ) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)) ^ 2)‖ ≤ 2 := by
      intro i _
      rw [smul_eq_mul, norm_mul, norm_prod, Finset.prod_eq_one fun l _ => norm_blaschke_eq_one w hw _ (a_re_pos ε l), one_mul]
      exact (hasDerivAt_blaschke w hw _ (a_re_pos ε i)).2
    calc ∑ i ∈ Finset.range j, ‖(∏ l ∈ (Finset.range j).erase i,
            ((w - ((1 + ε + 2 * l : ℕ) : ℂ)) / (w + ((1 + ε + 2 * l : ℕ) : ℂ)))) •
          (2 * ((1 + ε + 2 * i : ℕ) : ℂ) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)) ^ 2)‖
        ≤ ∑ i ∈ Finset.range j, (2 : ℝ) := Finset.sum_le_sum hterm
      _ = 2 * j := by rw [Finset.sum_const, Finset.card_range]; simp [mul_comm]

end Ws31.AxisR

theorem solution (k : ℤ) (ε j : ℕ) :
    let N : ℂ → ℂ := fun w => (-Complex.I) ^ k *
        ((∏ i ∈ Finset.range j, ((w + 1 - (ε : ℂ)) / 2 - 1 - (i : ℂ))) / (Real.pi : ℂ) ^ j) *
        Complex.Gammaℝ (w + 1 + (ε : ℂ)) * (Complex.Gammaℝ (w + 1 + ((ε + 2 * j : ℕ) : ℂ)))⁻¹
    (∀ w : ℂ, -1 < w.re → N w = (-Complex.I) ^ k *
        ∏ i ∈ Finset.range j, ((w - ((1 + ε + 2 * i : ℕ) : ℂ)) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)))) ∧
    (∀ w : ℂ, w.re = 0 → ‖N w‖ = 1 ∧ DifferentiableAt ℂ N w ∧ ‖deriv N w‖ ≤ 2 * j) :=
  Ws31.AxisR.main k ε j

end S_AutomorphicForm_archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero (solution)
