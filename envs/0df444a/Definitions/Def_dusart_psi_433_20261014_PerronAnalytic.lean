-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronAnalytic
-- name    : dusart_psi_433_20261014_PerronAnalytic
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:35:10.065248+00:00
-- url     : https://prove2.me/theorems/ff20b61c-4a94-4dc6-9687-adaef34970c1
-- title:
--   Dusart smoothing: Perron Analytic
-- statement:
--   This module gives the complete perron analytic component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PerronResidues
noncomputable section
namespace DusartSmoothing
open Complex Set Topology Filter Asymptotics Real
open DusartSmoothing.Contour

lemma zeta_nonzero_left_half_strip (s : ℂ) (hlo : -(1 / 2 : ℝ) ≤ s.re)
    (hi : s.re ≤ 0) : riemannZeta s ≠ 0 := by
  by_cases hs : s = 0
  · subst s; rw [riemannZeta_zero]; norm_num
  have hΓ : Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    have hr := congrArg Complex.re hn
    simp at hr
    have hn0 : n = 0 := by
      by_contra hh
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh
      linarith
    subst n
    simp at hn
    exact hs hn
  rw [riemannZeta_def_of_ne_zero hs]
  exact div_ne_zero (RvM.completedRiemannZeta_ne_zero_of_re_nonpos hi) hΓ

lemma zeta_zero_iff_nontrivial_in_half_strip (s : ℂ) (hs : -(1 / 2 : ℝ) ≤ s.re) :
    riemannZeta s = 0 ↔ RvM.IsNontrivialZero s := by
  constructor
  · intro hz
    have hp : 0 < s.re := by
      by_contra hh
      exact zeta_nonzero_left_half_strip s hs (le_of_not_gt hh) hz
    have h1 : s.re < 1 := by
      by_contra hh
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hh) hz
    exact ⟨hz, hp, h1⟩
  · exact fun h => h.1

lemma perronIntegrand_analyticAt (x : ℝ) (hx : 0 < x) (s : ℂ)
    (hlo : -(1 / 2 : ℝ) ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : AnalyticAt ℂ (perronIntegrand x) s := by
  have ha : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hb : s + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hK := quadraticKernel_analyticAt x hx s h0 ha hb
  have hZ := RvM.analyticAt_riemannZeta h1
  exact hK.neg.mul (hZ.deriv.div hZ hζ)

end DusartSmoothing


