-- Prove2me | Definitions.Def_dusart_psi_433_20261014_KernelIntegrals
-- name    : dusart_psi_433_20261014_KernelIntegrals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:18:20.431794+00:00
-- url     : https://prove2.me/theorems/21608faa-5870-496b-9318-d77e1c7ce6f1
-- title:
--   Dusart smoothing: Kernel Integrals
-- statement:
--   This module gives the complete kernel integrals component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Construction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set MeasureTheory

namespace DusartSmoothing

noncomputable def lowerEnvelope (X a u : ℝ) : ℝ :=
  u ^ 2 * (u - a) / X ^ 2 * Real.exp (-X ^ 2 / u)

noncomputable def lowerDerivative (X a u : ℝ) : ℝ :=
  Real.exp (-X ^ 2 / u) * ((u - a) + (3 * u ^ 2 - 2 * a * u) / X ^ 2)

lemma hasDerivAt_lowerEnvelope (X a u : ℝ) (hX : X ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (lowerEnvelope X a) (lowerDerivative X a u) u := by
  have hp := (((hasDerivAt_id u).pow 2).mul ((hasDerivAt_id u).sub_const a)).div_const (X ^ 2)
  have he := ((hasDerivAt_const u (-X ^ 2)).div (hasDerivAt_id u) hu).exp
  convert hp.mul he using 1
  all_goals first
    | rfl
    | (dsimp [lowerEnvelope, lowerDerivative]; field_simp [hX, hu]; ring)

lemma lowerDerivative_ge (X a u : ℝ) (hu : 0 < u) (ha : a ≤ u) :
    (u - a) * Real.exp (-X ^ 2 / u) ≤ lowerDerivative X a u := by
  have hnum : 0 ≤ 3 * u ^ 2 - 2 * a * u := by
    have hh := mul_nonneg hu.le (sub_nonneg.mpr ha)
    nlinarith
  have hc : 0 ≤ (3 * u ^ 2 - 2 * a * u) / X ^ 2 :=
    div_nonneg hnum (sq_nonneg X)
  have hm := mul_nonneg (Real.exp_pos (-X ^ 2 / u)).le hc
  dsimp [lowerDerivative]
  nlinarith only [hm]

lemma lowerEnvelope_nonneg (X a u : ℝ) (ha : a ≤ u) : 0 ≤ lowerEnvelope X a u := by
  dsimp [lowerEnvelope]
  exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg u) (sub_nonneg.mpr ha))
    (sq_nonneg X)) (Real.exp_pos _).le

theorem lower_kernel_integral_bound (X a u₀ b : ℝ) (hX : 0 < X)
    (hu₀ : 0 < u₀) (ha : a ≤ u₀) (hb : u₀ ≤ b) :
    (∫ u in u₀..b, (u - a) * Real.exp (-X ^ 2 / u)) ≤ lowerEnvelope X a b := by
  have hg : ContinuousOn (lowerEnvelope X a) (Icc u₀ b) := by
    intro u hu
    exact (hasDerivAt_lowerEnvelope X a u hX.ne'
      (ne_of_gt (hu₀.trans_le hu.1))).continuousAt.continuousWithinAt
  have hφ : ContinuousOn (fun u : ℝ => (u - a) * Real.exp (-X ^ 2 / u)) (Icc u₀ b) := by
    intro u hu
    have hun : u ≠ 0 := ne_of_gt (hu₀.trans_le hu.1)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hi : IntegrableOn (fun u : ℝ => (u - a) * Real.exp (-X ^ 2 / u)) (Icc u₀ b) :=
    hφ.integrableOn_Icc
  have hh := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hb hg
    (fun u hu => (hasDerivAt_lowerEnvelope X a u hX.ne'
      (ne_of_gt (hu₀.trans hu.1))).hasDerivWithinAt) hi
    (fun u hu => lowerDerivative_ge X a u (hu₀.trans hu.1) (ha.trans hu.1.le))
  have hp := lowerEnvelope_nonneg X a u₀ ha
  linarith

noncomputable def upperEnvelope (X a u : ℝ) : ℝ :=
  u ^ 2 * (u - a + 1 / 2) / (2 * u ^ 2 - X ^ 2) *
    Real.exp (-2 * u + (-X ^ 2 / u))

noncomputable def upperDerivative (X a u : ℝ) : ℝ :=
  Real.exp (-2 * u + (-X ^ 2 / u)) *
    (-(u - a) - X ^ 2 * (2 * u ^ 2 - (4 * a - 2) * u + X ^ 2) /
      (2 * (2 * u ^ 2 - X ^ 2) ^ 2))

lemma hasDerivAt_upperEnvelope (X a u : ℝ) (hu : u ≠ 0)
    (hD : 2 * u ^ 2 - X ^ 2 ≠ 0) :
    HasDerivAt (upperEnvelope X a) (upperDerivative X a u) u := by
  have hn := ((hasDerivAt_id u).pow 2).mul
    (((hasDerivAt_id u).sub_const a).add_const (1 / 2))
  have hd := (((hasDerivAt_id u).pow 2).const_mul 2).sub_const (X ^ 2)
  have he := (((hasDerivAt_id u).const_mul (-2)).add
    ((hasDerivAt_const u (-X ^ 2)).div (hasDerivAt_id u) hu)).exp
  convert (hn.div hd hD).mul he using 1
  all_goals first
    | rfl
    | (dsimp [upperEnvelope, upperDerivative]; field_simp [hu, hD]; ring)

lemma neg_upperDerivative_ge (X a u : ℝ) (hu : 0 ≤ u) (ha : 2 * a - 1 ≤ u) :
    (u - a) * Real.exp (-2 * u + (-X ^ 2 / u)) ≤ -upperDerivative X a u := by
  have hq : 0 ≤ 2 * u ^ 2 - (4 * a - 2) * u + X ^ 2 := by
    have hh := mul_nonneg hu (sub_nonneg.mpr ha)
    nlinarith [sq_nonneg X]
  have hc : 0 ≤ X ^ 2 * (2 * u ^ 2 - (4 * a - 2) * u + X ^ 2) /
      (2 * (2 * u ^ 2 - X ^ 2) ^ 2) := by positivity
  have hm := mul_nonneg (Real.exp_pos (-2 * u + (-X ^ 2 / u))).le hc
  dsimp [upperDerivative]
  nlinarith only [hm]

lemma upperEnvelope_nonneg (X a u : ℝ) (ha : a ≤ u) (hD : 0 ≤ 2 * u ^ 2 - X ^ 2) :
    0 ≤ upperEnvelope X a u := by
  dsimp [upperEnvelope]
  exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg u) (by linarith)) hD)
    (Real.exp_pos _).le

theorem upper_kernel_integral_bound (X a u₀ b : ℝ) (hu₀ : 0 < u₀)
    (ha : a ≤ u₀) (ha' : 2 * a - 1 ≤ u₀) (hD₀ : 0 < 2 * u₀ ^ 2 - X ^ 2)
    (hb : u₀ ≤ b) :
    (∫ u in u₀..b, (u - a) * Real.exp (-2 * u + (-X ^ 2 / u))) ≤ upperEnvelope X a u₀ := by
  have hD : ∀ u ∈ Icc u₀ b, 0 < 2 * u ^ 2 - X ^ 2 := by
    intro u hu
    nlinarith [hu.1]
  have hg : ContinuousOn (fun u => -upperEnvelope X a u) (Icc u₀ b) := by
    intro u hu
    exact (hasDerivAt_upperEnvelope X a u (ne_of_gt (hu₀.trans_le hu.1))
      (ne_of_gt (hD u hu))).neg.continuousAt.continuousWithinAt
  have hφ : ContinuousOn (fun u : ℝ => (u - a) * Real.exp (-2 * u + (-X ^ 2 / u))) (Icc u₀ b) := by
    intro u hu
    have hun : u ≠ 0 := ne_of_gt (hu₀.trans_le hu.1)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hi : IntegrableOn (fun u : ℝ => (u - a) * Real.exp (-2 * u + (-X ^ 2 / u))) (Icc u₀ b) :=
    hφ.integrableOn_Icc
  have hh := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hb hg
    (fun u hu => (hasDerivAt_upperEnvelope X a u (ne_of_gt (hu₀.trans hu.1))
      (ne_of_gt (hD u ⟨hu.1.le, hu.2.le⟩))).neg.hasDerivWithinAt) hi
    (fun u hu => neg_upperDerivative_ge X a u (hu₀.trans hu.1).le
      (ha'.trans hu.1.le))
  have hp := upperEnvelope_nonneg X a b (ha.trans hb) (hD b ⟨hb, le_rfl⟩).le
  linarith

lemma upper_kernel_continuousOn (X a u₀ b : ℝ) (hu₀ : 0 < u₀) :
    ContinuousOn (fun u : ℝ => (u - a) * Real.exp (-2 * u + (-X ^ 2 / u)))
      (Icc u₀ b) := by
  intro u hu
  have hun : u ≠ 0 := ne_of_gt (hu₀.trans_le hu.1)
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)

theorem upper_kernel_integrable (X a u₀ : ℝ) (hu₀ : 0 < u₀)
    (ha : a ≤ u₀) (ha' : 2 * a - 1 ≤ u₀) (hD₀ : 0 < 2 * u₀ ^ 2 - X ^ 2) :
    IntegrableOn (fun u : ℝ => (u - a) * Real.exp (-2 * u + (-X ^ 2 / u)))
      (Ioi u₀) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (upperEnvelope X a u₀) u₀
    (fun b : ℝ => (upper_kernel_continuousOn X a u₀ b hu₀).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self) Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop u₀] with b hb
  have heq : (∫ u in u₀..b, ‖(u - a) * Real.exp (-2 * u + (-X ^ 2 / u))‖) =
      ∫ u in u₀..b, (u - a) * Real.exp (-2 * u + (-X ^ 2 / u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hb] at hu
    exact Real.norm_of_nonneg (mul_nonneg (sub_nonneg.mpr (ha.trans hu.1))
      (Real.exp_pos _).le)
  rw [heq]
  exact upper_kernel_integral_bound X a u₀ b hu₀ ha ha' hD₀ hb

theorem upper_kernel_improper_integral_bound (X a u₀ : ℝ) (hu₀ : 0 < u₀)
    (ha : a ≤ u₀) (ha' : 2 * a - 1 ≤ u₀) (hD₀ : 0 < 2 * u₀ ^ 2 - X ^ 2) :
    (∫ u in Ioi u₀, (u - a) * Real.exp (-2 * u + (-X ^ 2 / u))) ≤
      upperEnvelope X a u₀ := by
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi u₀
    (upper_kernel_integrable X a u₀ hu₀ ha ha' hD₀) Filter.tendsto_id)
  filter_upwards [Filter.eventually_ge_atTop u₀] with b hb
  exact upper_kernel_integral_bound X a u₀ b hu₀ ha ha' hD₀ hb

lemma lowerEnvelope_at_parameter (X ν : ℝ) (hX : X ≠ 0) (hν : ν ≠ 0) :
    lowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) =
      X * G0 X ν * Real.exp (-X / ν) := by
  dsimp [lowerEnvelope, G0]
  congr 1
  · field_simp
    try ring
  · congr 1
    field_simp
    try ring

lemma upperEnvelope_at_parameter (X ν : ℝ) (hX : X ≠ 0) (hν : ν ≠ 0)
    (_hD : 2 * ν ^ 2 - 1 ≠ 0) :
    upperEnvelope X (Real.log (2 * Real.pi)) (X * ν) =
      X * G1 X ν * Real.exp (-(2 * ν + 1 / ν) * X) := by
  dsimp [upperEnvelope, G1]
  congr 1
  · field_simp
    ring
  · congr 1
    field_simp
    ring

end DusartSmoothing


