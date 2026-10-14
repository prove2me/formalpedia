-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronKernelConj
-- name    : dusart_psi_433_20261014_PerronKernelConj
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:33:55.594987+00:00
-- url     : https://prove2.me/theorems/4be51284-7a91-4d45-aab5-a90975661127
-- title:
--   Dusart smoothing: Perron Kernel Conj
-- statement:
--   This module gives the complete perron kernel conj component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PerronResidues
import Definitions.Def_dusart_psi_433_20261014_ZeroConjugation
noncomputable section
namespace DusartSmoothing
open Complex

lemma quadraticKernel_conj (x : ℝ) (hx : 0 < x) (s : ℂ) :
    quadraticKernel x (starRingEnd ℂ s) = starRingEnd ℂ (quadraticKernel x s) := by
  have he : starRingEnd ℂ s + 2 = starRingEnd ℂ (s + 2) := by simp [map_add, map_ofNat]
  rw [quadraticKernel, quadraticKernel, he, RvM.cpow_ofReal_conj hx]
  simp only [map_div₀, map_mul, map_add, map_one, map_ofNat]

lemma norm_weighted_quadratic_conj (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : s ≠ 1) :
    ‖(RvM.zeroMult (starRingEnd ℂ s) : ℂ) * quadraticKernel x (starRingEnd ℂ s)‖ =
      ‖(RvM.zeroMult s : ℂ) * quadraticKernel x s‖ := by
  rw [RvM.zeroMult_conj s hs, quadraticKernel_conj x hx s]
  have he : (RvM.zeroMult s : ℂ) * starRingEnd ℂ (quadraticKernel x s) =
      starRingEnd ℂ ((RvM.zeroMult s : ℂ) * quadraticKernel x s) := by simp
  rw [he, Complex.norm_conj]

end DusartSmoothing


