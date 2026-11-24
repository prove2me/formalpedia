-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEulerRecurrence
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEulerRecurrence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:20:43.407353+00:00
-- url     : https://prove2.me/theorems/adc262ca-9609-4c83-b021-8b6dd39efb11
-- title:
--   Truncated Euler products for the split quadratic character
-- statement:
--   Identify the finite set of monic primes of degree d with the subtype of monic irreducible polynomials whose natural degree is d. For a finite root set s and cutoff N, define the truncated Euler product over all monic primes of degree at most N, using the weighted geometric series of each prime's split quadratic character weight and degree. Define the matching rate series as the sum of the degree-weighted prime-rate series over the same primes. These are finite formal power-series constructions.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitEulerRecurrence.lean lines 16–39; SHA256 157a10eb48313caa62edfab622927587fa6160e359ea79adda6da10e88322064; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_EulerNewtonIdentity
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finsupp.Weight
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



/-! The exact Newton recurrence for the actual split quadratic-character L-polynomial. -/

open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def splitEulerProduct (s : Finset K) (N : ℕ) : ℤ⟦X⟧ :=
  ∏ P ∈ primesUpTo (K := K) N,
    weightedGeometric (splitQuadraticWeight s P) (P : K[X]).natDegree

def splitEulerRate (s : Finset K) (N : ℕ) : ℤ⟦X⟧ :=
  ∑ P ∈ primesUpTo (K := K) N,
    weightedPrimeRate (splitQuadraticWeight s P) (P : K[X]).natDegree



def primeDegreeSubtypeEquiv (d : ℕ) :
    {P : MonicPrime K // P ∈ primesOfDegree d} ≃
      {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d} where
  toFun P := ⟨P.1.1, P.1.2.1, P.1.2.2, (mem_primesOfDegree d P.1).mp P.2⟩
  invFun P := ⟨⟨P.1, P.2.1, P.2.2.1⟩,
    (mem_primesOfDegree d ⟨P.1, P.2.1, P.2.2.1⟩).mpr P.2.2.2⟩
  left_inv P := rfl
  right_inv P := rfl















end
end PaleyWeil


