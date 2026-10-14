-- Prove2me | Definitions.Def_dusart_psi_433_20261014_CountTailEnvelope
-- name    : dusart_psi_433_20261014_CountTailEnvelope
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:07.071541+00:00
-- url     : https://prove2.me/theorems/ef28b8d6-f993-4b4f-a25d-b8286903fdfb
-- title:
--   Dusart smoothing: Count Tail Envelope
-- statement:
--   This module gives the complete count tail envelope component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_KernelIntegrals
noncomputable section
namespace DusartSmoothing
open Real Set MeasureTheory

noncomputable def gaussianCountTailEnvelope (X u : ℝ) : ℝ :=
  Real.exp (-3 * u + (-X^2 / u)) / (3 - X^2 / u^2)

lemma gaussian_count_error_kernel_bound (X a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 < 3 - X^2 / a^2) :
    (∫ u in a..b, Real.exp (-3 * u + (-X^2 / u))) ≤ gaussianCountTailEnvelope X a := by
  let D : ℝ := 3 - X^2 / a^2
  let J : ℝ → ℝ := fun u => Real.exp (-3 * u + (-X^2 / u)) / D
  have hd : ∀ u : ℝ, u ≠ 0 → HasDerivAt (fun y => -J y)
      (Real.exp (-3 * u + (-X^2 / u)) * (3 - X^2 / u^2) / D) u := by
    intro u hu
    convert (((((hasDerivAt_id u).const_mul (-3)).add
      ((hasDerivAt_const u (-X^2)).div (hasDerivAt_id u) hu)).exp).div_const D).neg using 1 <;> try rfl
    dsimp [J]
    field_simp <;> ring
  have hc : ContinuousOn (fun u => -J u) (Icc a b) := fun u hu =>
    (hd u (ha.trans_le hu.1).ne').continuousAt.continuousWithinAt
  have hφ : ContinuousOn (fun u => Real.exp (-3 * u + (-X^2 / u))) (Icc a b) := by
    intro u hu
    have hn : u ≠ 0 := (ha.trans_le hu.1).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hc
    (fun u hu => (hd u (ha.trans hu.1).ne').hasDerivWithinAt) hφ.integrableOn_Icc
    (fun u hu => by
      have hp : 0 < u := ha.trans hu.1
      have hq : X^2 / u^2 ≤ X^2 / a^2 := div_le_div_of_nonneg_left
        (sq_nonneg X) (sq_pos_of_pos ha) (by nlinarith [hu.1])
      apply (le_div_iff₀ hD).2
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _))
  have hJ : 0 ≤ J b := div_nonneg (Real.exp_nonneg _) hD.le
  change (∫ u in a..b, Real.exp (-3 * u + (-X^2 / u))) ≤ J a
  linarith

end DusartSmoothing


