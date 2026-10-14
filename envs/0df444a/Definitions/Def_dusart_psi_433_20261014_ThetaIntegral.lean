-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ThetaIntegral
-- name    : dusart_psi_433_20261014_ThetaIntegral
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:24:36.032201+00:00
-- url     : https://prove2.me/theorems/5eb62a82-c531-4b0e-8343-a8024df6586a
-- title:
--   Dusart smoothing: Theta Integral
-- statement:
--   This module gives the complete theta integral component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ThetaSharp
noncomputable section
namespace DusartSmoothing.LowHeight
open Complex Real Set MeasureTheory

def thetaTail (x : ℝ) : ℝ := Real.exp (-Real.pi * x) / Real.sqrt x

def thetaEnvelope (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x) * Real.sqrt x / (Real.pi * x + 3 / 8)

def thetaEnvelopeDeriv (x : ℝ) : ℝ :=
  -thetaTail x * ((Real.pi * x)^2 + 7 / 8 * Real.pi * x - 3 / 16) /
    (Real.pi * x + 3 / 8)^2

lemma hasDerivAt_thetaEnvelope (x : ℝ) (hx : 0 < x) :
    HasDerivAt thetaEnvelope (thetaEnvelopeDeriv x) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have he := ((hasDerivAt_id x).const_mul (-Real.pi)).exp
  have hd := ((hasDerivAt_id x).const_mul Real.pi).add_const (3 / 8)
  have hp : 0 < Real.pi * x + 3 / 8 := by positivity
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h := (he.mul hs).div hd hp.ne'
  convert h using 1 <;> try rfl
  dsimp [thetaEnvelopeDeriv, thetaTail]
  field_simp [hspos.ne', hp.ne']
  ring_nf
  simp only [Real.sq_sqrt hx.le]
  ring

lemma neg_thetaEnvelopeDeriv_ge (x : ℝ) (hx : 1 ≤ x) :
    thetaTail x ≤ -thetaEnvelopeDeriv x := by
  have hx0 : 0 < x := by linarith
  have hd : 0 < (Real.pi * x + 3 / 8)^2 := by positivity
  have ht : 0 < thetaTail x := by dsimp [thetaTail]; positivity
  have hp : (Real.pi * x + 3 / 8)^2 ≤
      (Real.pi * x)^2 + 7 / 8 * Real.pi * x - 3 / 16 := by
    have hπ := Real.pi_gt_three
    have hpx : 3 ≤ Real.pi * x := by nlinarith
    nlinarith
  have hr : 1 ≤ ((Real.pi * x)^2 + 7 / 8 * Real.pi * x - 3 / 16) /
      (Real.pi * x + 3 / 8)^2 := (le_div_iff₀ hd).2 (by simpa using hp)
  calc thetaTail x ≤ thetaTail x * (((Real.pi * x)^2 +
        7 / 8 * Real.pi * x - 3 / 16) / (Real.pi * x + 3 / 8)^2) := by nlinarith
    _ = -thetaEnvelopeDeriv x := by dsimp [thetaEnvelopeDeriv]; ring

lemma thetaTail_continuousOn (b : ℝ) : ContinuousOn thetaTail (Icc 1 b) := by
  intro x hx
  have hxp : 0 < x := by linarith [hx.1]
  apply ContinuousAt.continuousWithinAt
  unfold thetaTail
  have hn := (Real.sqrt_pos.2 hxp).ne'
  fun_prop (disch := assumption)

lemma thetaTail_integrable : IntegrableOn thetaTail (Ioi 1) := by
  have he : IntegrableOn (fun x : ℝ => Real.exp (-Real.pi * x)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) 1
  have hc : ContinuousOn thetaTail (Ioi 1) := by
    intro x hx
    have hxp : 0 < x := lt_trans zero_lt_one hx
    apply ContinuousAt.continuousWithinAt
    unfold thetaTail
    have hn := (Real.sqrt_pos.2 hxp).ne'
    fun_prop (disch := assumption)
  apply he.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hs : 1 ≤ Real.sqrt x := (Real.one_le_sqrt).2 hx.le
  rw [Real.norm_of_nonneg (by dsimp [thetaTail]; positivity)]
  dsimp [thetaTail]
  exact div_le_self (Real.exp_pos _).le hs

lemma thetaTail_finite_integral_bound (b : ℝ) (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, thetaTail x) ≤ thetaEnvelope 1 := by
  have hg : ContinuousOn (fun x => -thetaEnvelope x) (Icc 1 b) := by
    intro x hx
    exact (hasDerivAt_thetaEnvelope x (by linarith [hx.1])).fun_neg.continuousAt.continuousWithinAt
  have hi := (thetaTail_continuousOn b).integrableOn_Icc (μ := volume)
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hb hg
    (fun x hx => (hasDerivAt_thetaEnvelope x (by linarith [hx.1])).fun_neg.hasDerivWithinAt) hi
    (fun x hx => neg_thetaEnvelopeDeriv_ge x hx.1.le)
  have hnonneg : 0 ≤ thetaEnvelope b := by dsimp [thetaEnvelope]; positivity
  linarith

lemma thetaTail_integral_bound : (∫ x in Ioi 1, thetaTail x) ≤
    Real.exp (-Real.pi) / (Real.pi + 3 / 8) := by
  have h : (∫ x in Ioi 1, thetaTail x) ≤ thetaEnvelope 1 := by
    apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 1 thetaTail_integrable Filter.tendsto_id)
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with b hb
    exact thetaTail_finite_integral_bound b hb
  simpa [thetaEnvelope] using h

end DusartSmoothing.LowHeight


