-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659Histogram
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659Histogram
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:58.492331+00:00
-- url     : https://prove2.me/theorems/7e00356d-6118-4d55-a3e3-3654c4de87ba
-- title:
--   Signed Paley histograms and elementary character moments
-- statement:
--   For a finite Paley-field set H and a point x, define the indicator that x belongs to H and the j-th elementary character moment, the sum of products of the signs χ(x−a) over all j-element subsets of H. A histogram with n nonzero signs, of which p are positive, is represented by (X+1)^p (X−1)^(n−p). Its j-th moment is the coefficient of X^(n−j) when j ≤ n, and zero otherwise. An explicit finite binomial sum gives an integer formula for this coefficient.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659Histogram.lean lines 10–26; SHA256 d1365f3b3a5318a1946afcf3b585cdc6d0dc15c4850368d2aca9862c8d7b8ae6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



open Finset Polynomial

namespace PaleyWeil

noncomputable section

def paleyInside (H : Finset PaleyField) (x : PaleyField) : ℕ := if x ∈ H then 1 else 0

def paleyElementaryMoment (H : Finset PaleyField) (j : ℕ) (x : PaleyField) : ℤ :=
  ∑ A ∈ H.powersetCard j, ∏ a ∈ A, paleySign a x

def signedHistogramPolynomial (n p : ℕ) : ℤ[X] := (X + 1) ^ p * (X - 1) ^ (n - p)

def signedHistogramMoment (n p j : ℕ) : ℤ :=
  if j ≤ n then (signedHistogramPolynomial n p).coeff (n - j) else 0

/-- An entirely computable integer expression for the histogram coefficient. -/
def signedHistogramMomentExplicit (n p j : ℕ) : ℤ :=
  if j ≤ n then
    ∑ i ∈ Finset.range (n - j + 1),
      (Nat.choose p i : ℤ) *
        ((-1 : ℤ) ^ (n - p - (n - j - i)) * (Nat.choose (n - p) (n - j - i) : ℤ))
  else 0


















end
end PaleyWeil


