-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronResidues
-- name    : dusart_psi_433_20261014_PerronResidues
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:32:49.419406+00:00
-- url     : https://prove2.me/theorems/8bb71fbc-a069-420a-9dd3-bd7801284a35
-- title:
--   Dusart smoothing: Perron Residues
-- statement:
--   This module gives the complete perron residues component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PoleParts
import Definitions.Def_dusart_psi_433_20261014_SymmetricWindows
import Definitions.Def_dusart_psi_433_20261014_Perron
noncomputable section
namespace DusartSmoothing
open Complex Set Topology Filter Asymptotics Real
open DusartSmoothing.Contour

def quadraticKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ)^(s + 2) / (s * (s + 1) * (s + 2))

def perronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -quadraticKernel x s * logDeriv riemannZeta s

lemma quadraticKernel_analyticAt (x : ℝ) (hx : 0 < x) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s + 1 ≠ 0) (h2 : s + 2 ≠ 0) :
    AnalyticAt ℂ (quadraticKernel x) s := by
  have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : Differentiable ℂ (fun s : ℂ => (x : ℂ)^(s + 2)) :=
    fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hn)
  exact (hp.analyticAt s).div (by fun_prop) (mul_ne_zero (mul_ne_zero h0 h1) h2)

lemma quadraticKernel_at_one (x : ℝ) : quadraticKernel x 1 = (x : ℂ)^3 / 6 := by
  norm_num [quadraticKernel]

lemma quadraticKernel_eq_mellin (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    quadraticKernel x s = mellin (quadraticPrimeWeight x) s :=
  (mellin_quadraticPrimeWeight x hx s hs).symm

lemma perron_zero_principal_part (x : ℝ) (hx : 0 < x) (ρ : ℂ)
    (hρ : RvM.IsNontrivialZero ρ) :
    (perronIntegrand x - fun s =>
      -((RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ) / (s - ρ))
      =O[𝓝[≠] ρ] (1 : ℂ → ℂ) := by
  have h0 : ρ ≠ 0 := by
    intro h
    have hh := hρ.2.1
    rw [h] at hh
    norm_num at hh
  have h1 : ρ + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith [hρ.2.1]
  have h2 : ρ + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith [hρ.2.1]
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hh := hρ.2.2
    rw [h] at hh
    norm_num at hh
  have h := weighted_logDeriv_principal_part
    (RvM.analyticAt_riemannZeta hρ1) (quadraticKernel_analyticAt x hx ρ h0 h1 h2).neg
  change ((fun s => -quadraticKernel x s * logDeriv riemannZeta s) -
    fun s => -((RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ) / (s - ρ)) =O[𝓝[≠] ρ] (1 : ℂ → ℂ)
  simpa only [Pi.neg_apply, RvM.zeroMult, mul_neg] using h


lemma perron_one_principal_part (x : ℝ) (hx : 0 < x) :
    (perronIntegrand x - fun s => ((x : ℂ)^3 / 6) / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hf : ∀ᶠ s in 𝓝[≠] (1 : ℂ), AnalyticAt ℂ riemannZeta s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact RvM.analyticAt_riemannZeta (by simpa using hs)
  have h := weighted_logDeriv_pole_principal_part (m := 1) hf one_ne_zero
    (by simpa only [pow_one] using riemannZeta_residue_one)
    (quadraticKernel_analyticAt x hx 1 (by norm_num) (by norm_num) (by norm_num)).neg
  change ((fun s => -quadraticKernel x s * logDeriv riemannZeta s) -
    fun s => ((x : ℂ)^3 / 6) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ)
  simpa only [Pi.neg_apply, Nat.cast_one, one_mul, neg_neg,
    quadraticKernel_at_one] using h

def perronZeroNumerator (x : ℝ) (s : ℂ) : ℂ :=
  -(x : ℂ)^(s + 2) * logDeriv riemannZeta s / ((s + 1) * (s + 2))

lemma perronIntegrand_eq_div (x : ℝ) (s : ℂ) :
    perronIntegrand x s = perronZeroNumerator x s / s := by
  simp only [perronIntegrand, quadraticKernel, perronZeroNumerator, div_eq_mul_inv, mul_inv_rev]
  ring

lemma perronZeroNumerator_analyticAt_zero (x : ℝ) (hx : 0 < x) :
    AnalyticAt ℂ (perronZeroNumerator x) 0 := by
  have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : AnalyticAt ℂ (fun s : ℂ => (x : ℂ)^(s + 2)) 0 :=
    (show Differentiable ℂ (fun s : ℂ => (x : ℂ)^(s + 2)) from
      fun s => (differentiableAt_id.add_const 2).const_cpow (Or.inl hn)).analyticAt 0
  have hζ := RvM.analyticAt_riemannZeta (by norm_num : (0 : ℂ) ≠ 1)
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hl : AnalyticAt ℂ (logDeriv riemannZeta) 0 := hζ.deriv.div hζ hζ0
  exact (hp.neg.mul hl).div (by fun_prop) (by norm_num)

lemma perronZeroNumerator_at_zero (x : ℝ) :
    perronZeroNumerator x 0 = -(x : ℂ)^2 / 2 * logDeriv riemannZeta 0 := by
  norm_num [perronZeroNumerator]
  ring

lemma perron_zero_kernel_principal_part (x : ℝ) (hx : 0 < x) :
    (perronIntegrand x - fun s =>
      (-(x : ℂ)^2 / 2 * logDeriv riemannZeta 0) / s)
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have h := analytic_div_principal_part (perronZeroNumerator_analyticAt_zero x hx)
  simpa only [sub_zero, perronZeroNumerator_at_zero,
    ← perronIntegrand_eq_div] using h

end DusartSmoothing


