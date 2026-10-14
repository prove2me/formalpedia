-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaEMDefs
-- name    : dusart_psi_433_20261014_ZetaEMDefs
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:16:05.877441+00:00
-- url     : https://prove2.me/theorems/b2b4a4ce-728a-4507-997b-58dbe445c303
-- title:
--   Dusart smoothing: Zeta Euler–Maclaurin Defs
-- statement:
--   This module gives the complete zeta euler–maclaurin defs component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic

noncomputable section
namespace DusartSmoothing.ZetaEM

def B1 (x : ℝ) : ℝ := x - (⌊x⌋₊ : ℝ) - 1/2
def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N+1), 1/(n:ℂ)^s) +
  (- (N:ℂ)^(1-s))/(1-s) + (-(N:ℂ)^(-s))/2 +
  s * ∫ x in Set.Ioi (N:ℝ), ((⌊x⌋:ℂ)+1/2-x)/(x:ℂ)^(s+1)
def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), -1/(n:ℂ)^s * Real.log n +
  (-(N:ℂ)^(1-s)/(1-s)^2 + Real.log N * (N:ℂ)^(1-s)/(1-s)) +
  Real.log N * (N:ℂ)^(-s)/2 +
  ((∫ x in Set.Ioi (N:ℝ), ((⌊x⌋:ℂ)+1/2-x)*(x:ℂ)^(-s-1)) +
  s * ∫ x in Set.Ioi (N:ℝ), ((⌊x⌋:ℂ)+1/2-x)*(x:ℂ)^(-s-1)*(-Real.log x))

end DusartSmoothing.ZetaEM


