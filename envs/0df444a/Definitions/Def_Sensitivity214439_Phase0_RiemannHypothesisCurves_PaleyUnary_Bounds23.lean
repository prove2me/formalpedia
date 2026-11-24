-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds23
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds23
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:27:38.034501+00:00
-- url     : https://prove2.me/theorems/3b30ae7a-2167-47f5-956d-0d60767b336e
-- title:
--   Paley histogram coefficient vectors for sets of size $23$
-- statement:
--   Fix the high-set size $h=23$ in the Paley field $\mathbb{F}_{2659}$. This bundle records the exact integer coefficient vectors for the queried failure allowances $k\in\{0,1,2,3,4,5\}$. Each stored vector has the form
--
--   $$c^{(h,k)}=(c_0,\ldots,c_{26})\in\mathbb{Z}^{27}.$$
--
--   The feature basis begins with the outside indicator, inside indicator, and internal incidence count. The remaining available indices use ordinary low-degree moments followed by signed character moments. The companion population lemmas use these literal vectors to verify a pointwise majorant for the desired prefix population and an exact upper bound for the sum of that majorant.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PaleyUnary/Bounds23.lean lines 19–60; SHA256 cb557f7c3e9f21bf76094e5f2b3efabc3460d682b3262f11fbcb480daea991da; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def paleyUnaryCoefficients_23_0 : Fin 27 → ℤ := ![-7557, -7833, 28, 2552, -592, 72, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]



def paleyUnaryCoefficients_23_1 : Fin 27 → ℤ := ![11, 0, 2, 198, -76, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11]



def paleyUnaryCoefficients_23_2 : Fin 27 → ℤ := ![241, 220, 2, -42, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]



def paleyUnaryCoefficients_23_3 : Fin 27 → ℤ := ![241, 220, 2, -42, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]



def paleyUnaryCoefficients_23_4 : Fin 27 → ℤ := ![241, 220, 2, -42, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]



def paleyUnaryCoefficients_23_5 : Fin 27 → ℤ := ![55, 55, 0, -10, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]





end PaleyWeil


