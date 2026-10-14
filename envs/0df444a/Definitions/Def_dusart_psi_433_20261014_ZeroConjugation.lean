-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroConjugation
-- name    : dusart_psi_433_20261014_ZeroConjugation
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:47.303713+00:00
-- url     : https://prove2.me/theorems/0bb342f0-b1f7-4632-b26e-30853daf5a25
-- title:
--   Dusart smoothing: Zero Conjugation
-- statement:
--   This module gives the complete zero conjugation component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ContourSymmetry
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set Topology Filter

lemma deriv_of_conj_symmetry (f : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (s : ℂ) :
    deriv f (starRingEnd ℂ s) = starRingEnd ℂ (deriv f s) := by
  have h : ∀ z : ℂ, starRingEnd ℂ (f (starRingEnd ℂ z)) = f z := by
    intro z
    rw [hf, Complex.conj_conj]
  simp [← deriv_conj_conj' f, h]

lemma iteratedDeriv_riemannZeta_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (iteratedDeriv n riemannZeta s) := by
  induction n generalizing s with
  | zero => simp only [iteratedDeriv_zero]; exact riemannZeta_conj s
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact deriv_of_conj_symmetry (iteratedDeriv n riemannZeta) ih s

lemma zeroMult_conj (s : ℂ) (hs : s ≠ 1) :
    zeroMult (starRingEnd ℂ s) = zeroMult s := by
  have hcs : starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs
    rw [← Complex.conj_conj s, h, map_one]
  have hf := analyticAt_riemannZeta hs
  have hc := analyticAt_riemannZeta hcs
  have he : analyticOrderAt riemannZeta (starRingEnd ℂ s) = analyticOrderAt riemannZeta s := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hc,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    simp only [iteratedDeriv_riemannZeta_conj, map_eq_zero]
  simp only [zeroMult, analyticOrderNatAt, he]

end DusartSmoothing.RvM


