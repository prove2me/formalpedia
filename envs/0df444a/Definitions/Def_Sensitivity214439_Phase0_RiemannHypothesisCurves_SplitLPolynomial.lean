-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLPolynomial
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLPolynomial
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:59:56.053348+00:00
-- url     : https://prove2.me/theorems/2bf178b7-99dd-4462-a847-312ed5a16318
-- title:
--   The complex polynomial of split character coefficients
-- statement:
--   For a finite root set s, define a complex polynomial whose coefficient in each degree i < |s| is the integer split character coefficient of degree i, embedded into the complex numbers, and whose higher coefficients are zero. This is the finite polynomial on which the root-amplification argument operates.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitLPolynomial.lean lines 16–18; SHA256 3bc3e34c144b78fa80f5e7ed7fd547a9d2d7db02e951eab3028ce85d715a5bb6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
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
open scoped PowerSeries

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The actual polynomial obtained from the vanishing character coefficients. -/
def splitLPolynomial (s : Finset K) : ℂ[X] :=
  Polynomial.ofFn s.card (fun i ↦ (splitLCoeff s i : ℂ))












end
end PaleyWeil


