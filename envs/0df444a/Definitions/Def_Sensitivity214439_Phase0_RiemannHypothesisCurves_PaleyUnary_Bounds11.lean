-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds11
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyUnary_Bounds11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:15:26.436854+00:00
-- url     : https://prove2.me/theorems/d44ebdbc-0540-4c2c-92e6-1c6d4c78c09d
-- title:
--   Paley histogram coefficient vectors for sets of size $11$
-- statement:
--   Fix the high-set size $h=11$ in the Paley field $\mathbb{F}_{2659}$. This bundle records the exact integer coefficient vectors for the queried failure allowances $k\in\{0,1,2,3,4,5\}$. Each stored vector has the form
--
--   $$c^{(h,k)}=(c_0,\ldots,c_{14})\in\mathbb{Z}^{15}.$$
--
--   The feature basis begins with the outside indicator, inside indicator, and internal incidence count. The remaining available indices use ordinary low-degree moments followed by signed character moments. The companion population lemmas use these literal vectors to verify a pointwise majorant for the desired prefix population and an exact upper bound for the sum of that majorant.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PaleyUnary/Bounds11.lean lines 19–59; SHA256 e436652fd9984453e01f2fc60b3cb1564bb0161c94227f5bafd030a94e3f4830; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def paleyUnaryCoefficients_11_0 : Fin 15 → ℤ := ![21, -6, 6, 18, -20, 8, 0, 1, 0, 0, 0, 0, 0, 0, -1]



def paleyUnaryCoefficients_11_1 : Fin 15 → ℤ := ![-2655, -2537, 2, 1900, -1020, 320, 0, 15, 0, 0, 0, 0, 0, -5, 0]



def paleyUnaryCoefficients_11_2 : Fin 15 → ℤ := ![5, 0, 2, 30, -28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 5]



def paleyUnaryCoefficients_11_3 : Fin 15 → ℤ := ![31, 40, -2, -14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]



def paleyUnaryCoefficients_11_4 : Fin 15 → ℤ := ![39, 31, 2, -16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]



def paleyUnaryCoefficients_11_5 : Fin 15 → ℤ := ![263, 520, -114, -178, 128, -28, 0, 0, 0, 0, 0, 0, 0, 0, -85]





end PaleyWeil


