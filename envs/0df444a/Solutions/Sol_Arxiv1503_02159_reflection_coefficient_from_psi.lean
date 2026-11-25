-- Prove2me | solution 1 for Arxiv1503_02159.reflection_coefficient_from_psi
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:56:13.747003+00:00
-- url     : https://prove2.me/submissions/0c41c7a3-556b-4204-9efc-9cef409e5857

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology
open Arxiv1503_02159

lemma second_deriv_neg {k : ℝ} {ψ : ℝ → ℂ} {v : ℝ → ℝ} (hcont : Continuous ψ)
    (hv0 : ∀ x, x < 0 → v x = 0)
    (hint : ∀ a b : ℝ, deriv ψ b - deriv ψ a = ∫ t in a..b, ((v t : ℂ) - (k : ℂ) ^ 2) * ψ t)
    {y : ℝ} (hy : y < 0) : HasDerivAt (deriv ψ) (-(k : ℂ) ^ 2 * ψ y) y := by
  set a := y - 1 with ha
  have hc : Continuous (fun t => -(k : ℂ) ^ 2 * ψ t) := continuous_const.mul hcont
  have hg : HasDerivAt (fun z => deriv ψ a + ∫ t in a..z, -(k : ℂ) ^ 2 * ψ t)
      (-(k : ℂ) ^ 2 * ψ y) y := by
    have := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a y)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    exact this.const_add (deriv ψ a)
  apply hg.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hy] with z hz
  have h := hint a z
  have hcongr : ∫ t in a..z, ((v t : ℂ) - (k : ℂ) ^ 2) * ψ t = ∫ t in a..z, -(k : ℂ) ^ 2 * ψ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t < 0 := by
      rcases Set.mem_uIcc.mp ht with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact lt_of_le_of_lt h2 hz
      · linarith
    simp [hv0 t ht0]
  rw [hcongr] at h
  linear_combination h

lemma hasDerivAt_cexp_mul (c : ℂ) (z : ℝ) :
    HasDerivAt (fun z : ℝ => Complex.exp (c * z)) (Complex.exp (c * z) * c) z := by
  have h1 : HasDerivAt (fun z : ℝ => c * (z : ℂ)) c z := by
    simpa using ((hasDerivAt_id z).ofReal_comp).const_mul c
  exact h1.cexp

lemma two_exp_vanish (κ c1 c2 : ℂ) (k : ℝ) (hk : 0 < k) (hκ : κ = (k : ℂ) * Complex.I)
    (h : Tendsto (fun x : ℝ => c1 * Complex.exp (κ * x) + c2 * Complex.exp (-κ * x)) atBot (𝓝 0)) :
    c1 = 0 ∧ c2 = 0 := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set u : ℕ → ℝ := fun n => -(2 * Real.pi * n / k)
  have hu : Tendsto u atTop atBot := by
    apply tendsto_neg_atTop_atBot.comp
    apply Tendsto.atTop_div_const hk
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hw : Tendsto (fun n => u n - Real.pi / (2 * k)) atTop atBot :=
    tendsto_atBot_add_const_right _ _ hu
  have e1 : ∀ n : ℕ, κ * (u n : ℂ) = -(n * (2 * Real.pi * Complex.I)) := by
    intro n; simp only [u, hκ]; push_cast; field_simp
  have e2 : ∀ n : ℕ, κ * ((u n - Real.pi / (2 * k) : ℝ) : ℂ) =
      -(n * (2 * Real.pi * Complex.I)) - (Real.pi / 2 : ℂ) * Complex.I := by
    intro n; simp only [u, hκ]; push_cast; field_simp
    try ring
  have hn1 : ∀ n : ℕ, Complex.exp (n * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_nat_mul_two_pi_mul_I
  have hI : Complex.exp ((Real.pi / 2 : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I]
    rw [show ((Real.pi / 2 : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have s1 := h.comp hu
  have s2 := h.comp hw
  have v1 : ∀ n : ℕ, (fun x : ℝ => c1 * Complex.exp (κ * x) + c2 * Complex.exp (-κ * x)) (u n)
      = c1 + c2 := by
    intro n
    simp only [neg_mul, e1, Complex.exp_neg, hn1, neg_neg]
    simp
  have v2 : ∀ n : ℕ, (fun x : ℝ => c1 * Complex.exp (κ * x) + c2 * Complex.exp (-κ * x))
      (u n - Real.pi / (2 * k)) = -Complex.I * c1 + Complex.I * c2 := by
    intro n
    simp only [neg_mul, e2, Complex.exp_neg, Complex.exp_sub, hn1, neg_sub, sub_neg_eq_add,
      Complex.exp_add, hI]
    field_simp
    try simp [Complex.I_sq]
    try ring_nf
    try simp [Complex.I_sq]
    try ring
  have l1 : c1 + c2 = 0 := by
    have : (fun x : ℝ => c1 * Complex.exp (κ * x) + c2 * Complex.exp (-κ * x)) ∘ u =
        fun _ => c1 + c2 := funext v1
    rw [this] at s1
    exact tendsto_nhds_unique tendsto_const_nhds s1
  have l2 : -Complex.I * c1 + Complex.I * c2 = 0 := by
    have : (fun x : ℝ => c1 * Complex.exp (κ * x) + c2 * Complex.exp (-κ * x)) ∘
        (fun n : ℕ => u n - Real.pi / (2 * k)) = fun _ => -Complex.I * c1 + Complex.I * c2 :=
      funext v2
    rw [this] at s2
    exact tendsto_nhds_unique tendsto_const_nhds s2
  have l3 : c2 - c1 = 0 := by
    have : Complex.I * (c2 - c1) = 0 := by linear_combination l2
    exact (mul_eq_zero.mp this).resolve_left Complex.I_ne_zero
  constructor
  · linear_combination (l1 - l3) / 2
  · linear_combination (l1 + l3) / 2

theorem solution (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (x : ℝ) (hx : x < 0) :
    s21 = Complex.exp (k * x * Complex.I) * ψ x - Complex.exp (2 * k * x * Complex.I) := by
  obtain ⟨hdiff, hint, -, hbot, -⟩ := hψ
  obtain ⟨-, -, hv0⟩ := hv
  have hcont := hdiff.continuous
  set κ : ℂ := (k : ℂ) * Complex.I with hκ
  have hκ2 : κ ^ 2 = -(k : ℂ) ^ 2 := by rw [hκ, mul_pow, Complex.I_sq]; ring
  have hκ0 : κ ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') Complex.I_ne_zero
  have hrw : ∀ y : ℝ, (k : ℂ) * y * Complex.I = κ * y := fun y => by rw [hκ]; ring
  have e2x : Complex.exp (2 * k * x * Complex.I) = Complex.exp (κ * x) * Complex.exp (κ * x) := by
    rw [← Complex.exp_add]; congr 1; rw [hκ]; ring
  have hbot' : Tendsto (fun y : ℝ => ψ y - (Complex.exp (κ * y) + s21 * Complex.exp (-κ * y)))
      atBot (𝓝 0) := by
    simpa only [hrw, neg_mul] using hbot
  rw [hrw x, e2x]
  have hκ' := hκ
  clear_value κ
  have hψd : ∀ z, HasDerivAt ψ (deriv ψ z) z := fun z => (hdiff z).hasDerivAt
  set F : ℝ → ℂ := fun z => Complex.exp (-κ * z) * (deriv ψ z + κ * ψ z) with hF
  set G : ℝ → ℂ := fun z => Complex.exp (κ * z) * (deriv ψ z - κ * ψ z) with hG
  have hFd : ∀ z, z < 0 → HasDerivAt F 0 z := by
    intro z hz
    have := (hasDerivAt_cexp_mul (-κ) z).mul
      ((second_deriv_neg hcont hv0 hint hz).add ((hψd z).const_mul κ))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination (-(Complex.exp (-κ * z) * ψ z)) * hκ2
  have hGd : ∀ z, z < 0 → HasDerivAt G 0 z := by
    intro z hz
    have := (hasDerivAt_cexp_mul κ z).mul
      ((second_deriv_neg hcont hv0 hint hz).sub ((hψd z).const_mul κ))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination (-(Complex.exp (κ * z) * ψ z)) * hκ2
  have hconst : ∀ (H : ℝ → ℂ), (∀ z, z < 0 → HasDerivAt H 0 z) → ∀ z, z < 0 → H z = H (-1) := by
    intro H hH z hz
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun y hy => (hH y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hH y hy).deriv) hz (show (-1 : ℝ) < 0 by norm_num)
  set A : ℂ := F (-1) / (2 * κ)
  set B : ℂ := -G (-1) / (2 * κ)
  have hform : ∀ z : ℝ, z < 0 → ψ z = A * Complex.exp (κ * z) + B * Complex.exp (-κ * z) := by
    intro z hz
    have h1 := hconst F hFd z hz
    have h2 := hconst G hGd z hz
    simp only [hF, hG] at h1 h2
    have e1 : Complex.exp (κ * z) * Complex.exp (-κ * z) = 1 := by
      rw [← Complex.exp_add]; simp
    have key : 2 * κ * ψ z = F (-1) * Complex.exp (κ * z) - G (-1) * Complex.exp (-κ * z) := by
      simp only [hF, hG]
      linear_combination Complex.exp (κ * z) * h1 - Complex.exp (-κ * z) * h2 - 2 * κ * ψ z * e1
    simp only [A, B]
    field_simp
    simp only [neg_mul] at key ⊢
    linear_combination key
  have hlim : Tendsto (fun y : ℝ => (A - 1) * Complex.exp (κ * y) + (B - s21) * Complex.exp (-κ * y))
      atBot (𝓝 0) := by
    apply hbot'.congr'
    filter_upwards [Iio_mem_atBot (0 : ℝ)] with y hy
    rw [hform y hy]
    ring
  obtain ⟨hA, hB⟩ := two_exp_vanish κ (A - 1) (B - s21) k hk hκ' hlim
  have hψx := hform x hx
  have e1 : Complex.exp (κ * x) * Complex.exp (-κ * x) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [hψx]
  have hA' : A = 1 := by linear_combination hA
  have hB' : B = s21 := by linear_combination hB
  rw [hA', hB']
  linear_combination -s21 * e1

