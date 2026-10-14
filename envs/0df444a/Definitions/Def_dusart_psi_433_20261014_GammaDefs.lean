-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaDefs
-- name    : dusart_psi_433_20261014_GammaDefs
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:16:04.584058+00:00
-- url     : https://prove2.me/theorems/090c2f06-5881-4d58-93dd-ae6a70d75c53
-- title:
--   Dusart smoothing: Gamma Defs
-- statement:
--   This module gives the complete gamma defs component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

noncomputable section
namespace DusartSmoothing.StirlingVert
def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m+1), ((x-m:ℝ):ℂ)^2 / (((m:ℂ)+w)^2*((x:ℂ)+w))
def rho (w : ℂ) (n : ℕ) : ℂ :=
  1 / (((n:ℂ)+1+w)^2*((n:ℂ)+2+w))
end DusartSmoothing.StirlingVert


