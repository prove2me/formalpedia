-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaSeriesDefs
-- name    : dusart_psi_433_20261014_GammaSeriesDefs
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:28.500222+00:00
-- url     : https://prove2.me/theorems/3f68a37e-7ebb-4895-b150-24d3a2c62c02
-- title:
--   Dusart smoothing: Gamma Series Defs
-- statement:
--   This module gives the complete gamma series defs component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_dusart_psi_433_20261014_GammaDefs
noncomputable section
namespace DusartSmoothing.DigammaSeries
def wTerm (n : ℕ) (z : ℂ) : ℂ :=
  (1 + z/(n+1)) * Complex.exp (-(z/(n+1))) - 1
end DusartSmoothing.DigammaSeries


