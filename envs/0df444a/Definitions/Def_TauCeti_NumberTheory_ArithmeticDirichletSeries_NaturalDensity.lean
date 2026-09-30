-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NaturalDensity
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_NaturalDensity
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:53:32.794309+00:00
-- url     : https://prove2.me/theorems/788e90bb-b7a0-4977-98d1-5aeaee466f88
-- title:
--   Natural density of sets of prime ideals
-- statement:
--   For a number field $K$ and a set $S$ of its nonzero prime ideals, define natural density $\delta$ by
--
--   $$
--   \lim_{x\to\infty}\frac{\#\{P\in S:\mathrm N P\leq x\}}{\#\{P:\mathrm N P\leq x\}}=\delta.
--   $$
--
--   This is density relative to all prime ideals, using inclusive real norm bounds.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/NaturalDensity.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/NaturalDensity.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
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
# Natural density of sets of prime ideals

For a number field `K`, this file defines the natural density of a set `S` of nonzero prime
ideals as the limit

```text
  primeCount K S x / primeCount K Set.univ x
```

as the inclusive real cutoff `x` tends to infinity. This normalization matches Mathlib's
ratio-normalized `NumberField.Set.HasDirichletDensity`: a density is measured relative to all
prime ideals of the same number field, rather than relative to an external approximation such as
`x / log x`.

The denominator really tends to infinity. Indeed, lying over supplies a prime of `𝓞 K` above
every rational prime, so the height-one spectrum is infinite. Its bounded-norm subsets are finite
and exhaust the spectrum, whence their cardinalities tend to infinity. This fact both makes the
whole spectrum have density one and ensures that a fixed finite error disappears in the ratio.

## Main results

* `NumberField.Set.HasNaturalDensity`: ratio-normalized natural density for a set of prime ideals.
* `NumberField.Set.hasNaturalDensity_def`: the defining ratio-convergence characterization.
* `NumberField.Set.HasNaturalDensity.union`,
  `NumberField.Set.hasNaturalDensity_biUnion_finset` and
  `NumberField.Set.HasNaturalDensity.compl`: finite Boolean calculus for natural density.
* `NumberField.Set.HasNaturalDensity.of_finite_symmDiff`: changing a prime set on finitely many
  primes preserves its natural density.
* `NumberField.Set.hasNaturalDensity_of_finite`: every finite set of prime ideals has natural
  density zero.
* `NumberField.Set.hasNaturalDensity_of_isLittleO_logIntegral`: if all primes satisfy
  `π(x) = Li(x) + o(x / log x)` and the primes of `S` satisfy `π_S(x) = δ Li(x) + o(x / log x)`,
  then `S` has natural density `δ`.
* `NumberField.Set.isUpperDirichletDensityBound_of_eventually_primeCount_le` and
  `NumberField.Set.isLowerDirichletDensityBound_of_eventually_le_primeCount`: an eventual
  one-sided bound on the proportion of primes of `S` below `x` is the same one-sided bound for
  Dirichlet density.
* `NumberField.Set.hasDirichletDensity_of_hasNaturalDensity`: natural density implies Dirichlet
  density, with the same value.

The comparison with Dirichlet density rests on two inputs. Abel summation against the decreasing
function `t ↦ t ^ (-s)` (`TauCeti.tsum_mul_le_of_summatory_le`) turns an eventual bound
`π_S(x) ≤ c · π(x)` into a bound `P_S(s) ≤ c · P(s) + C` with `C` independent of `s > 1`, where
`P_S` is Mathlib's `NumberField.Set.primeIdealZetaSum S`. The all-prime sum `P(s)` tends to
infinity as `s → 1⁺` (`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), so the constant `C`
disappears from the ratio `P_S(s) / P(s)`.

The definition, its elementary calculus, and the comparison with Dirichlet density are standard;
see J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4, J.-P. Serre, *Corps locaux*, Chapter
VI, or J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Set

open Filter IsDedekindDomain
open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set `S` of height-one primes of a number field has natural density `δ` when the proportion
of primes of `S` below `x`, relative to all primes below `x`, tends to `δ` as `x → ∞`.

Both counts use the inclusive real cutoff fixed by `TauCeti.primeCount`. -/
def HasNaturalDensity (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
    TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ)





























/-! ### Natural density implies Dirichlet density -/

















end NumberField.Set

end
end


