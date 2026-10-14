-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LandauSplit
-- name    : dusart_psi_433_20261014_LandauSplit
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:22:07.438973+00:00
-- url     : https://prove2.me/theorems/9855b07f-fc67-4a2e-abf1-7bbe6f8a2f82
-- title:
--   Dusart smoothing: Landau Split
-- statement:
--   This module gives the complete landau split component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LandauFactor
/- Copyright (c) 2026 Anthropic PBC; Apache-2.0. -/
noncomputable section
namespace DusartSmoothing.Landau
open Complex Set Metric Filter Topology

/-- Away from the zero set, `f = Π (z−ρ)^{m_ρ} · Cf`. -/
lemma f_eq_prod_mul_Cf {f : ℂ → ℂ} {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : z ∉ SetOfZeros r f) :
    f z = (∏ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset, (z - ρ) ^ analyticOrderNatAt f ρ)
      * Cf r f z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  unfold Cf
  rw [dif_pos hfinr, dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  have hρ' := hfinr.mem_toFinset.mp hρ
  have hne : z ≠ ρ := by
    rintro rfl
    exact hz hρ'
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)

/-- logDeriv of the finite zero product: `logDeriv (Π (·−ρ)^{m_ρ}) z = Σ m_ρ/(z−ρ)`
(Mathlib's `logDeriv_prod` + `logDeriv_fun_pow`). -/
lemma logDeriv_zero_prod {s : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ ρ ∈ s, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ s, (w - ρ) ^ m ρ) z = ∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))) (fun ρ _ => by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring







theorem logDeriv_split {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) + logDeriv (Cf r f) z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  set P0 : ℂ → ℂ := fun w => ∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ with hP0
  have hU : IsOpen (Metric.ball (0 : ℂ) r \ SetOfZeros r f) :=
    Metric.isOpen_ball.sdiff hfinr.isClosed
  have hzU : z ∈ Metric.ball (0 : ℂ) r \ SetOfZeros r f :=
    ⟨mem_ball_zero_iff.mpr hz, fun h => hfz h.2⟩
  have heq : f =ᶠ[nhds z] fun w => P0 w * Cf r f w := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact f_eq_prod_mul_Cf hr1 hfin hw.2
  have hzne : ∀ ρ ∈ hfinr.toFinset, z ≠ ρ := by
    intro ρ hρ
    rintro rfl
    exact hfz (hfinr.mem_toFinset.mp hρ).2
  have hP0z : P0 z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have hCfz : Cf r f z ≠ 0 := Cf_ne_zero hfa hf0 hr1 hfin hz.le
  have hdP0 : DifferentiableAt ℂ P0 z :=
    DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have hdCf : DifferentiableAt ℂ (Cf r f) z := by
    have hR : r < (r + 1) / 2 := by linarith
    have hR1 : (r + 1) / 2 < 1 := by linarith
    exact ((CfAnalytic hR hR1 hfa hf0) z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      calc ‖z‖ ≤ r := hz.le
        _ ≤ (r + 1) / 2 := by linarith)).differentiableAt
  calc logDeriv f z = logDeriv (fun w => P0 w * Cf r f w) z := by
        unfold logDeriv
        simp only [Pi.div_apply]
        rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv P0 z + logDeriv (Cf r f) z := logDeriv_mul z hP0z hCfz hdP0 hdCf
    _ = _ := by rw [hP0, logDeriv_zero_prod hzne]

end DusartSmoothing.Landau


