-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:48:20.447937+00:00
-- url     : https://prove2.me/theorems/8596a6e4-4100-4c1f-87b3-66366a483d8b
-- title:
--   Split character coefficients and degree-weighted prime sums
-- statement:
--   Over a finite field, define the n-th split character coefficient by summing the split quadratic weight over all monic polynomials of degree n. Define the associated prime sum by summing over divisors d of n: for each d, multiply d by the sum of the n/d-th powers of the weights of all monic irreducible polynomials of degree d. These integer quantities are the coefficient and logarithmic-derivative data for the split character L-series.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitLSeriesDefs.lean lines 9–19; SHA256 273ccae8c6467866080dcc2669d0772139aca182a047e0b736bc199f01e851cc; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



open Polynomial Finset

namespace PaleyWeil

/-- Coefficients of the polynomial-character L-series. -/
noncomputable def splitLCoeff {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) (n : ℕ) : ℤ :=
  ∑' P : {P : K[X] // IsMonicOfDegree P n}, splitQuadraticWeight s P

/-- The degree-weighted prime-polynomial sum in the logarithmic derivative. -/
noncomputable def splitLPrimeSum {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) *
    ∑' P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d},
      splitQuadraticWeight s P ^ (n / d)










end PaleyWeil


