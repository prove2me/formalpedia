-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds18
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds18
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:26:00.881256+00:00
-- url     : https://prove2.me/theorems/eb564d29-36f3-4564-b5cf-043c4a95cf21
-- title:
--   Paley histogram coefficient vectors for sets of size $18$
-- statement:
--   Fix the high-set size $h=18$ in the Paley field $\mathbb{F}_{2659}$. This bundle records the exact integer coefficient vectors for the queried failure allowances $k\in\{0,1,2,3,4,5\}$. Each stored vector has the form
--
--   $$c^{(h,k)}=(c_0,\ldots,c_{21})\in\mathbb{Z}^{22}.$$
--
--   The feature basis begins with the outside indicator, inside indicator, and internal incidence count. The remaining available indices use ordinary low-degree moments followed by signed character moments. The companion population lemmas use these literal vectors to verify a pointwise majorant for the desired prefix population and an exact upper bound for the sum of that majorant.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PaleyUnary/Bounds18.lean lines 19–60; SHA256 f22f374a220e5e02e30094196629f7b135a92a7a5305dd4c9123d865bee5fe5b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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



/-! Generated exact certificates for Paley2659 unary prefix populations.

Source: analysis/exact-no-quartic-prefix-certificates.json
SHA256: dc3ad7df3e611e464a1f7c632fda6cf4741ab8f9fa4fecbec6468ba3c73aa95f
Only the ordinary moments of degrees 1, 2, 3 and the proved signed Weil
intervals are used. No ordinary quartic codegree bound is assumed.
Every finite comparison below is checked by the Lean kernel with `decide`.
The original campaign checkpoint is preserved unchanged.
-/

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

open Finset
namespace PaleyWeil

def paleyUnaryCoefficients_18_0 : Fin 22 → ℤ := ![-1620, -1840, 28, 840, -280, 48, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]



def paleyUnaryCoefficients_18_1 : Fin 22 → ℤ := ![-1775, -1700, -6, 710, -204, 32, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5]



def paleyUnaryCoefficients_18_2 : Fin 22 → ℤ := ![0, 0, 0, 28, -14, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]



def paleyUnaryCoefficients_18_3 : Fin 22 → ℤ := ![36, 36, 0, -8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]



def paleyUnaryCoefficients_18_4 : Fin 22 → ℤ := ![127, 144, -2, -30, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]



def paleyUnaryCoefficients_18_5 : Fin 22 → ℤ := ![127, 144, -2, -30, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]





end PaleyWeil


