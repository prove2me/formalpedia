-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroReflection
-- name    : dusart_psi_433_20261014_ZeroReflection
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:31:46.190808+00:00
-- url     : https://prove2.me/theorems/72040bd1-af86-4822-8000-51fcef32b455
-- title:
--   Dusart smoothing: Zero Reflection
-- statement:
--   This module gives the complete zero reflection component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroConjugation
import Definitions.Def_dusart_psi_433_20261014_SymmetricWindows
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real

lemma nontrivial_zero_conj {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (starRingEnd ℂ ρ) := by
  refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩
  rw [riemannZeta_conj, hρ.1, map_zero]

lemma nontrivial_zero_one_sub {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - ρ) := by
  apply completedRiemannZeta_eq_zero_iff.mp
  rw [completedRiemannZeta_one_sub]
  exact completedRiemannZeta_eq_zero_iff.mpr hρ

lemma zeroMult_one_sub (ρ : ℂ) (hρ : IsNontrivialZero ρ) : zeroMult (1 - ρ) = zeroMult ρ := by
  have hτ := nontrivial_zero_one_sub hρ
  have hρ1 : ρ ≠ 1 := by intro h; have hh := hρ.2.2; simp [h] at hh
  have hτ1 : 1 - ρ ≠ 1 := by intro h; have hh := hτ.2.2; simp [h] at hh
  have hφ : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hd : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by
    have he : deriv (fun s : ℂ => 1 - s) ρ = -1 :=
      ((hasDerivAt_id ρ).const_sub 1).deriv
    rw [he]
    norm_num
  have hc := analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hφ hd
  have he : (completedRiemannZeta ∘ fun s : ℂ => 1 - s) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  rw [he] at hc
  have hn := congrArg ENat.toNat hc
  change analyticOrderNatAt completedRiemannZeta ρ =
    analyticOrderNatAt completedRiemannZeta (1 - ρ) at hn
  rw [analyticOrderNatAt_completedRiemannZeta hρ.2.1 hρ1,
    analyticOrderNatAt_completedRiemannZeta hτ.2.1 hτ1] at hn
  exact hn.symm

lemma nontrivial_zero_reflect {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - starRingEnd ℂ ρ) := nontrivial_zero_one_sub (nontrivial_zero_conj hρ)

lemma zeroMult_reflect (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    zeroMult (1 - starRingEnd ℂ ρ) = zeroMult ρ := by
  rw [zeroMult_one_sub _ (nontrivial_zero_conj hρ), zeroMult_conj ρ]
  intro h; have hh := hρ.2.2; simp [h] at hh

end DusartSmoothing.RvM


