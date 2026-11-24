-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:26:08.598111+00:00
-- url     : https://prove2.me/theorems/f3e1e624-7180-40c8-94a9-0e07fdc2c7e7
-- title:
--   Paley quadratic signs and common-neighbour counts
-- statement:
--   Use the field of residues modulo 2659 and define the sign from a to x to be the quadratic character of x−a. For a finite set H, define the number of positive signs at x and the total number of points receiving a positive sign from every member of H. Also define the product of 1 plus each sign and its sum over points internal to H. The latter records the correction contributed by the zero character values at members of H.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659LowMoments.lean lines 10–24; SHA256 b1cc8ff907c99775e8c087fc08f49a3d5f952bbb530041ee908e6e7ea0bf0b8c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CharacterBounds
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



open Finset

namespace PaleyWeil

noncomputable section

abbrev PaleyField := ZMod 2659

def paleySign (a x : PaleyField) : ℤ := quadraticChar PaleyField (x - a)

def paleyPositiveCount (H : Finset PaleyField) (x : PaleyField) : ℕ :=
  (H.filter (fun a ↦ paleySign a x = 1)).card

def paleyCommonCount (H : Finset PaleyField) : ℕ :=
  (Finset.univ.filter (fun x ↦ ∀ a ∈ H, paleySign a x = 1)).card

def paleyPlusProduct (H : Finset PaleyField) (x : PaleyField) : ℤ :=
  ∏ a ∈ H, (1 + paleySign a x)

def paleyInternalCorrection (H : Finset PaleyField) : ℤ :=
  ∑ x ∈ H, paleyPlusProduct H x

































end
end PaleyWeil


