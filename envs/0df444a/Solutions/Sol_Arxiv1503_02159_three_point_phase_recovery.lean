-- Prove2me | solution 1 for Arxiv1503_02159.three_point_phase_recovery
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:58:49.5022+00:00
-- url     : https://prove2.me/submissions/844880bb-1b5d-4249-b39b-2aeb14dfd4a0

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

theorem reflection_formula (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
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



lemma psi_neg_form (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (x : ℝ) (hx : x < 0) :
    ψ x = Complex.exp (k * x * Complex.I) + s21 * Complex.exp (-(k * x * Complex.I)) := by
  have h := reflection_formula v hv k hk ψ s21 s22 hψ x hx
  have e1 : Complex.exp (k * x * Complex.I) * Complex.exp (-(k * x * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have e2 : Complex.exp (2 * k * x * Complex.I) =
      Complex.exp (k * x * Complex.I) * Complex.exp (k * x * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e2] at h
  linear_combination (-Complex.exp (-(k * x * Complex.I))) * h + (Complex.exp (k * x * Complex.I) - ψ x) * e1

lemma phaseless_formula (ψ : ℝ → ℂ) (s21 : ℂ) (k x : ℝ)
    (hform : ψ x = Complex.exp (k * x * Complex.I) + s21 * Complex.exp (-(k * x * Complex.I))) :
    phaselessA ψ x = s21.re ^ 2 + s21.im ^ 2 + 2 * s21.re * Real.cos (2 * k * x) +
      2 * s21.im * Real.sin (2 * k * x) := by
  unfold phaselessA
  rw [hform, Complex.sq_norm, Complex.normSq_apply]
  have hre : (Complex.exp (k * x * Complex.I) + s21 * Complex.exp (-(k * x * Complex.I))).re =
      Real.cos (k * x) + s21.re * Real.cos (k * x) + s21.im * Real.sin (k * x) := by
    simp [Complex.add_re, Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im,
      Real.cos_neg, Real.sin_neg]
    ring
  have him : (Complex.exp (k * x * Complex.I) + s21 * Complex.exp (-(k * x * Complex.I))).im =
      Real.sin (k * x) - s21.re * Real.sin (k * x) + s21.im * Real.cos (k * x) := by
    simp [Complex.add_im, Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im,
      Real.cos_neg, Real.sin_neg]
    ring
  rw [hre, him, show 2 * k * x = 2 * (k * x) by ring, Real.cos_two_mul, Real.sin_two_mul]
  have hp := Real.sin_sq_add_cos_sq (k * x)
  linear_combination (1 + s21.re ^ 2 + s21.im ^ 2 - 2 * s21.re) * hp

lemma trig_key (u1 u2 u3 : ℝ) :
    2 * ((Real.sin (2 * u3) - Real.sin (2 * u1)) * (Real.cos (2 * u2) - Real.cos (2 * u1)) -
      (Real.sin (2 * u2) - Real.sin (2 * u1)) * (Real.cos (2 * u3) - Real.cos (2 * u1))) =
    8 * (Real.sin (u2 - u3) * Real.sin (u2 - u1) * Real.sin (u1 - u3)) := by
  rw [Real.sin_sub_sin, Real.sin_sub_sin, Real.cos_sub_cos, Real.cos_sub_cos]
  have a1 : (2 * u3 - 2 * u1) / 2 = u3 - u1 := by ring
  have a2 : (2 * u3 + 2 * u1) / 2 = u3 + u1 := by ring
  have a3 : (2 * u2 + 2 * u1) / 2 = u2 + u1 := by ring
  have a4 : (2 * u2 - 2 * u1) / 2 = u2 - u1 := by ring
  rw [a1, a2, a3, a4]
  have hs : Real.sin (u3 - u2) = Real.sin (u3 + u1) * Real.cos (u2 + u1) -
      Real.cos (u3 + u1) * Real.sin (u2 + u1) := by
    rw [← Real.sin_sub]; ring_nf
  have n1 : Real.sin (u2 - u3) = -Real.sin (u3 - u2) := by rw [← Real.sin_neg]; ring_nf
  have n2 : Real.sin (u1 - u3) = -Real.sin (u3 - u1) := by rw [← Real.sin_neg]; ring_nf
  rw [n1, n2, hs]
  ring

lemma sin_ne_of (k a b : ℝ) (hk : 0 < k) (h : ∀ n : ℤ, a - b ≠ n * (Real.pi / k)) :
    Real.sin (k * (a - b)) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h0
  apply h n
  field_simp
  linarith

theorem solution (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (α : ℝ) (hα : s21 = (‖s21‖ : ℂ) * Complex.exp (α * Complex.I))
    (x1 x2 x3 : ℝ) (hx1 : x1 < 0) (hx2 : x2 < 0) (hx3 : x3 < 0)
    (hx12 : ∀ n : ℤ, x1 - x2 ≠ n * (Real.pi / k))
    (hx13 : ∀ n : ℤ, x1 - x3 ≠ n * (Real.pi / k))
    (hx23 : ∀ n : ℤ, x2 - x3 ≠ n * (Real.pi / k)) :
    ‖s21‖ * Real.cos α = (8 * (Real.sin (k * (x2 - x3)) * Real.sin (k * (x2 - x1)) *
          Real.sin (k * (x1 - x3))))⁻¹ *
        ((Real.sin (2 * k * x3) - Real.sin (2 * k * x1)) * (phaselessA ψ x2 - phaselessA ψ x1)
          + (-Real.sin (2 * k * x2) + Real.sin (2 * k * x1)) *
            (phaselessA ψ x3 - phaselessA ψ x1)) ∧
    ‖s21‖ * Real.sin α = (8 * (Real.sin (k * (x2 - x3)) * Real.sin (k * (x2 - x1)) *
          Real.sin (k * (x1 - x3))))⁻¹ *
        ((-Real.cos (2 * k * x3) + Real.cos (2 * k * x1)) * (phaselessA ψ x2 - phaselessA ψ x1)
          + (Real.cos (2 * k * x2) - Real.cos (2 * k * x1)) *
            (phaselessA ψ x3 - phaselessA ψ x1)) := by
  have hX : ‖s21‖ * Real.cos α = s21.re := by
    conv_rhs => rw [hα]
    simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  have hY : ‖s21‖ * Real.sin α = s21.im := by
    conv_rhs => rw [hα]
    simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
  rw [hX, hY]
  have a1 := phaseless_formula ψ s21 k x1 (psi_neg_form v hv k hk ψ s21 s22 hψ x1 hx1)
  have a2 := phaseless_formula ψ s21 k x2 (psi_neg_form v hv k hk ψ s21 s22 hψ x2 hx2)
  have a3 := phaseless_formula ψ s21 k x3 (psi_neg_form v hv k hk ψ s21 s22 hψ x3 hx3)
  have hD : 8 * (Real.sin (k * (x2 - x3)) * Real.sin (k * (x2 - x1)) * Real.sin (k * (x1 - x3))) ≠ 0 := by
    have h1 := sin_ne_of k x2 x3 hk hx23
    have h2 : Real.sin (k * (x2 - x1)) ≠ 0 := by
      have := sin_ne_of k x1 x2 hk hx12
      rwa [show k * (x2 - x1) = -(k * (x1 - x2)) by ring, Real.sin_neg, neg_ne_zero]
    have h3 := sin_ne_of k x1 x3 hk hx13
    positivity
  have key := trig_key (k * x1) (k * x2) (k * x3)
  rw [show 2 * (k * x1) = 2 * k * x1 by ring, show 2 * (k * x2) = 2 * k * x2 by ring,
    show 2 * (k * x3) = 2 * k * x3 by ring, show k * x2 - k * x3 = k * (x2 - x3) by ring,
    show k * x2 - k * x1 = k * (x2 - x1) by ring, show k * x1 - k * x3 = k * (x1 - x3) by ring] at key
  rw [a1, a2, a3]
  constructor
  · rw [eq_inv_mul_iff_mul_eq₀ hD]
    linear_combination (-s21.re) * key
  · rw [eq_inv_mul_iff_mul_eq₀ hD]
    linear_combination (-s21.im) * key

