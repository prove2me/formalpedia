-- Prove2me | Definitions.Def_dusart_psi_433_20261014_SharperKernel
-- name    : dusart_psi_433_20261014_SharperKernel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:17.316335+00:00
-- url     : https://prove2.me/theorems/1678234e-3ca9-4519-abec-6f415b5b0948
-- title:
--   Dusart smoothing: Sharper Kernel
-- statement:
--   This module gives the complete sharper kernel component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Balance
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace DusartSmoothing

noncomputable def improvedLowerEnvelope (X a u : ℝ) : ℝ :=
  u ^ 2 * (u - a) / (X ^ 2 + 2 * u) * Real.exp (-X ^ 2 / u)

noncomputable def improvedLowerDerivative (X a u : ℝ) : ℝ :=
  Real.exp (-X ^ 2 / u) *
    ((u - a) + u ^ 2 * (X ^ 2 + 2 * a) / (X ^ 2 + 2 * u) ^ 2)

lemma hasDerivAt_improvedLowerEnvelope (X a u : ℝ) (hu : u ≠ 0)
    (hD : X ^ 2 + 2 * u ≠ 0) :
    HasDerivAt (improvedLowerEnvelope X a) (improvedLowerDerivative X a u) u := by
  have hn := ((hasDerivAt_id u).pow 2).mul ((hasDerivAt_id u).sub_const a)
  have hd := ((hasDerivAt_id u).const_mul 2).const_add (X ^ 2)
  have he := ((hasDerivAt_const u (-X ^ 2)).div (hasDerivAt_id u) hu).exp
  have hD₂ : u * X ^ 2 * 4 + u ^ 2 * 4 + X ^ 4 ≠ 0 := by
    have hid : u * X ^ 2 * 4 + u ^ 2 * 4 + X ^ 4 = (X ^ 2 + 2 * u) ^ 2 := by ring
    rw [hid]
    exact pow_ne_zero 2 hD
  have hcancel : (u * X ^ 2 * 4 + u ^ 2 * 4 + X ^ 4) *
      (u * X ^ 2 * 4 + u ^ 2 * 4 + X ^ 4)⁻¹ = 1 := mul_inv_cancel₀ hD₂
  convert (hn.div hd hD).mul he using 1
  all_goals first
    | rfl
    | (dsimp [improvedLowerEnvelope, improvedLowerDerivative]
       field_simp [hu, hD]
       ring_nf
       linear_combination -(u - a) * hcancel)

lemma improvedLowerDerivative_ge (X a u : ℝ) (ha : 0 ≤ a) :
    (u - a) * Real.exp (-X ^ 2 / u) ≤ improvedLowerDerivative X a u := by
  have hq : 0 ≤ u ^ 2 * (X ^ 2 + 2 * a) / (X ^ 2 + 2 * u) ^ 2 := by positivity
  have hm := mul_nonneg (Real.exp_pos (-X ^ 2 / u)).le hq
  dsimp [improvedLowerDerivative]
  nlinarith only [hm]

theorem improved_lower_kernel_integral_bound (X a b : ℝ) (ha : 0 < a) (hb : a ≤ b) :
    (∫ u in a..b, (u - a) * Real.exp (-X ^ 2 / u)) ≤ improvedLowerEnvelope X a b := by
  have hg : ContinuousOn (improvedLowerEnvelope X a) (Icc a b) := by
    intro u hu
    have hup : 0 < u := ha.trans_le hu.1
    have hD : 0 < X ^ 2 + 2 * u := by positivity
    exact (hasDerivAt_improvedLowerEnvelope X a u hup.ne' hD.ne').continuousAt.continuousWithinAt
  have hφ : ContinuousOn (fun u : ℝ => (u - a) * Real.exp (-X ^ 2 / u)) (Icc a b) := by
    intro u hu
    have hun : u ≠ 0 := (ha.trans_le hu.1).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hi : IntegrableOn (fun u : ℝ => (u - a) * Real.exp (-X ^ 2 / u)) (Icc a b) :=
    hφ.integrableOn_Icc
  have hh := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hb hg
    (fun u hu => by
      have hup : 0 < u := ha.trans hu.1
      have hD : 0 < X ^ 2 + 2 * u := by positivity
      exact (hasDerivAt_improvedLowerEnvelope X a u hup.ne' hD.ne').hasDerivWithinAt) hi
    (fun u hu => improvedLowerDerivative_ge X a u ha.le)
  simpa only [improvedLowerEnvelope, sub_self, mul_zero, zero_div, zero_mul, sub_zero] using hh

lemma improvedLowerEnvelope_relation (X a u : ℝ) (hX : X ≠ 0) :
    improvedLowerEnvelope X a u = lowerEnvelope X a u * X ^ 2 / (X ^ 2 + 2 * u) := by
  dsimp [improvedLowerEnvelope, lowerEnvelope]
  field_simp
  try ring

lemma improvedLowerEnvelope_at_parameter (X ν : ℝ) (hX : X ≠ 0) (hν : ν ≠ 0) :
    improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) =
      (X * G0 X ν * Real.exp (-X / ν)) * X / (X + 2 * ν) := by
  rw [improvedLowerEnvelope_relation X _ _ hX, lowerEnvelope_at_parameter X ν hX hν]
  field_simp
  try ring

theorem lower_balanced_envelope (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) :
    lowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) =
      optimalWidth X ν / 2 := by
  have hXp : X ≠ 0 := ne_of_gt (by linarith : 0 < X)
  have hνp : ν ≠ 0 := ne_of_gt (by linarith : 0 < ν)
  rw [lowerEnvelope_at_parameter X ν hXp hνp, lower_exponential_identity X ν hνp]
  dsimp [optimalWidth, balanceCoefficient]
  ring

theorem improved_balanced_envelope (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    (improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) +
      4 / optimalWidth X ν ^ 2 *
        upperEnvelope X (Real.log (2 * Real.pi)) (X * ν)) / (2 * Real.pi) =
      optimalWidth X ν - optimalWidth X ν * ν / (X + 2 * ν) := by
  have hXp : X ≠ 0 := ne_of_gt (by linarith : 0 < X)
  have hνp : 0 < ν := by linarith
  have hD : X + 2 * ν ≠ 0 := ne_of_gt (by linarith : 0 < X + 2 * ν)
  have he : improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) /
      (2 * Real.pi) = (optimalWidth X ν / 2) * X / (X + 2 * ν) := by
    rw [improvedLowerEnvelope_relation X _ _ hXp]
    have hr : X ^ 2 / (X ^ 2 + 2 * (X * ν)) = X / (X + 2 * ν) := by
      field_simp
      try ring
    calc
      _ = (lowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi)) *
          (X ^ 2 / (X ^ 2 + 2 * (X * ν))) := by ring
      _ = _ := by rw [hr, lower_balanced_envelope X ν hX hν]; ring
  have hb := balanced_kernel_envelopes X ν hX hν hν1 hk
  have hl := lower_balanced_envelope X ν hX hν
  rw [add_div, hl] at hb
  rw [add_div, he]
  have hu : (4 / optimalWidth X ν ^ 2 *
      upperEnvelope X (Real.log (2 * Real.pi)) (X * ν)) / (2 * Real.pi) =
        optimalWidth X ν / 2 := by linarith only [hb]
  rw [hu]
  field_simp
  ring

end DusartSmoothing


