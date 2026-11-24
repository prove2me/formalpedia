-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:49:48.623073+00:00
-- url     : https://prove2.me/theorems/a6c47c91-2f50-4beb-a36d-ba2d89427e1b
-- title:
--   Paley prefix populations and signed moment majorant data
-- statement:
--   For a finite set H, define its prefix population with a given failure allowance as the number of points outside H receiving at least |H| minus that allowance positive quadratic signs. Define the feature vector consisting of outside and inside indicators, the internal positive-sign count, binomial moments of orders 1 through 3, and higher elementary signed moments, together with the corresponding histogram formulas. Define lower and upper total-moment endpoints from the set size, low-degree codegree endpoints, and signed character centers and radii. Finally, define the signed endpoint rule that bounds a coefficient times a moment by using the upper endpoint for nonnegative coefficients and the lower endpoint for negative coefficients.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659PopulationMajorant.lean lines 10–43; SHA256 c655aaa1763972f3f4e511bbdbc4eeb242f70f5e111563c30ff800ced86807f8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659Histogram
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659MomentTotals
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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
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
import Mathlib.Tactic.IntervalCases
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



open Finset

namespace PaleyWeil

noncomputable section

def paleyPrefixCount (H : Finset PaleyField) (failures : ℕ) : ℕ :=
  (Finset.univ.filter (fun x ↦ x ∉ H ∧ H.card - failures ≤ paleyPositiveCount H x)).card

def paleyMomentFeature (H : Finset PaleyField) (i : ℕ) (x : PaleyField) : ℤ :=
  if i = 0 then (if x ∈ H then 0 else 1)
  else if i = 1 then (if x ∈ H then 1 else 0)
  else if i = 2 then (if x ∈ H then (paleyPositiveCount H x : ℤ) else 0)
  else if i ≤ 5 then (Nat.choose (paleyPositiveCount H x) (i - 2) : ℤ)
  else paleyElementaryMoment H (i - 3) x

def paleyHistogramFeature (h inside positives i : ℕ) : ℤ :=
  if i = 0 then 1 - (inside : ℤ)
  else if i = 1 then (inside : ℤ)
  else if i = 2 then (inside : ℤ) * (positives : ℤ)
  else if i ≤ 5 then (Nat.choose positives (i - 2) : ℤ)
  else signedHistogramMoment (h - inside) positives (i - 3)

def paleyMomentLower (h i : ℕ) : ℤ :=
  if i = 0 then 2659 - (h : ℤ)
  else if i = 1 then (h : ℤ)
  else if i = 2 then (Nat.choose h 2 : ℤ)
  else if i ≤ 5 then (Nat.choose h (i - 2) : ℤ) * paleyCodegreeLower (i - 2)
  else (Nat.choose h (i - 3) : ℤ) *
    (paleyCharacterCenter (i - 3) - paleyCharacterRadius (i - 3))

def paleyMomentUpper (h i : ℕ) : ℤ :=
  if i = 0 then 2659 - (h : ℤ)
  else if i = 1 then (h : ℤ)
  else if i = 2 then (Nat.choose h 2 : ℤ)
  else if i ≤ 5 then (Nat.choose h (i - 2) : ℤ) * paleyCodegreeUpper (i - 2)
  else (Nat.choose h (i - 3) : ℤ) *
    (paleyCharacterCenter (i - 3) + paleyCharacterRadius (i - 3))

def signedIntegerEndpoint (c lo hi : ℤ) : ℤ := if 0 ≤ c then c * hi else c * lo



















end
end PaleyWeil


