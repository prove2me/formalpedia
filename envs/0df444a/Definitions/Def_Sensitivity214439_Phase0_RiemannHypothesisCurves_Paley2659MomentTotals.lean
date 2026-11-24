-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659MomentTotals
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659MomentTotals
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:15:20.936155+00:00
-- url     : https://prove2.me/theorems/12a62913-2598-4eb4-bc27-47d194501cfc
-- title:
--   Integer centers, radii, and low-degree Paley endpoints
-- statement:
--   Define the parity-dependent character-sum center to be −1 in even degree and 0 in odd degree. The natural radius is the explicit integer expression 103132 times half of j−2 in even degree, or half of j−1 in odd degree, divided by 1000, using natural-number division and subtraction; its integer cast is also defined. The low-degree endpoint functions return 1329 for degree 1, 664 for degree 2, and respectively 319 and 344 in the remaining branch. These are the arithmetic parameters used by the later moment-bound proofs.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659MomentTotals.lean lines 91–159; SHA256 48456d750e106cb7d7428d46c5d32396fa06995c2bf45fc627d69eac0a4f335f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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











/-- A kernel-reducible formula for the exact integral Weil radius through degree 33.
The square-bracketing lemma below proves its equality with the natural square root. -/
def paleyCharacterRadiusNat (j : ℕ) : ℕ :=
  103132 * ((if j % 2 = 0 then j - 2 else j - 1) / 2) / 1000

def paleyCharacterRadius (j : ℕ) : ℤ := (paleyCharacterRadiusNat j : ℤ)





def paleyCharacterCenter (j : ℕ) : ℤ := if j % 2 = 0 then -1 else 0





def paleyCodegreeLower (j : ℕ) : ℤ := if j = 1 then 1329 else if j = 2 then 664 else 319
def paleyCodegreeUpper (j : ℕ) : ℤ := if j = 1 then 1329 else if j = 2 then 664 else 344









end
end PaleyWeil


