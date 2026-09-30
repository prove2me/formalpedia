-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:52:10.688988+00:00
-- url     : https://prove2.me/theorems/9be388fb-dfde-4384-90dd-7500d5902e8d
-- title:
--   Cancellation in ideal partial sums and the continued L-function of a weight
-- statement:
--   Let $\chi$ be a unitary ideal weight on a number field $K$, and put $d=[K:\mathbb Q]$. Cancellation means that a constant $C$ satisfies
--
--   $$
--   \left|\sum_{\mathrm N I\leq x}\chi(I)\right|\leq Cx^{1-1/d}\quad(x\geq1).
--   $$
--
--   The associated continuation is defined by the partial-summation integral $s\int_1^\infty A(t)t^{-s-1}\,dt$, where $A(t)$ is this ideal partial sum. This connects cancellation with analytic continuation.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Cancellation.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Cancellation.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

 section

namespace TauCeti

open Filter Asymptotics IsDedekindDomain MeasureTheory
open scoped ComplexConjugate nonZeroDivisors NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

/-- **Cancellation in the ideal partial sums of a unitary weight.** There is a constant `C` with
`‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / [K : ℚ])` for every real cutoff `x ≥ 1`, the sum running
over the nonzero integral ideals of absolute norm at most `x`. -/
def HasCancellation (χ : UnitaryIdealWeight K) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    ‖idealSummatory K χ.toIdealArithmeticFunction x‖ ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))













/-!
### Deleting finitely many Euler factors
-/





/-- **The continued L-function of a unitary weight**, defined by partial summation:
`s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

On `Re s > 1` it is the norm-regrouped L-series of `χ`
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`); under `TauCeti.HasCancellation χ` it is
holomorphic on `Re s > 1 - 1 / [K : ℚ]` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`).
Where the integral does not converge it takes the junk value of Mathlib's Bochner integral. -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ),
    idealSummatory K χ.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1))











/-!
### Conjugation and imaginary norm twists
-/







/-!
### The rejection test: weights that are norm twists on their good ideals
-/









end TauCeti

end
end


