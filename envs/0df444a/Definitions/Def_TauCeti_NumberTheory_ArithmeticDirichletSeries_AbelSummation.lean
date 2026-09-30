-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_AbelSummation
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_AbelSummation
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:42:58.431444+00:00
-- url     : https://prove2.me/theorems/e112f187-22f5-41b8-a1a0-8616d32c0955
-- title:
--   Abel summation for norm-indexed summatory functions
-- statement:
--   For a norm function $N$ with finite fibers and a weight $w$, the fiber-sum sequence is
--
--   $$
--   a(n)=\sum_{N(i)=n}w(i).
--   $$
--
--   This is the sequence used to apply ordinary Abel summation to norm-indexed counts.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/AbelSummation.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/AbelSummation.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
# Abel summation for norm-indexed summatory functions

Mathlib's `sum_mul_eq_sub_sub_integral_mul` is Abel summation for a sequence indexed by the natural
numbers.  Every counting argument of the arithmetic-Dirichlet-series roadmap instead sums a weight
over a carrier indexed by ideals or by height-one primes, cut off inclusively by the absolute norm.
This file supplies the bridge: the weight is regrouped into its norm fibres, Mathlib's identity is
applied to the resulting sequence, and the answer is read back as an equation between
`TauCeti.summatory` functions.

The bridge is stated for a general Northcott index `N : ι → ℕ`, because Layer 6 uses it for both
the ideal carrier and the prime carrier.  The integral runs over the half-open interval `Set.Ioc`,
so each boundary term is counted exactly once, as the roadmap's conventions table demands.

## Main results

* `TauCeti.summatory_mul_eq_sub_sub_integral_mul`: Abel summation between two nonnegative real
  cutoffs for a weight of the form `i ↦ w i * g (N i)`.
* `TauCeti.summatory_mul_eq_sub_integral_mul_of_le`: Abel summation from a real lower bound.
* `TauCeti.idealSummatory_mul_eq_sub_integral_mul`: the cutoff-`1` form for nonzero ideals.
* `TauCeti.primeSummatory_mul_eq_sub_integral_mul`: the cutoff-`2` form for the height-one primes
  of a number field.
* `TauCeti.norm_summatory_mul_cpow_le_of_summatory_le`: an imaginary-power twist preserves a
  positive power bound for partial sums, with an explicit constant.
* `TauCeti.integrableOn_mul_summatory`: a summatory function times an integrable factor is
  integrable on a compact interval, so the integrals above are genuine.
* `TauCeti.summatory_mul_le_of_summatory_le` and `TauCeti.tsum_mul_le_of_summatory_le`: for a
  nonnegative nonincreasing `g` and a carrier whose indices all have `N`-value at least `a ≥ 0`,
  an upper bound `C` on the partial sums of `w` gives the upper bound `C * g a` for the twisted
  partial sums and series.  This is how an eventual comparison of
  counting functions becomes a comparison of Dirichlet series uniform in `s`.
* `TauCeti.primeTheta_eq_log_mul_primeCount_sub_integral` and
  `TauCeti.primeCount_eq_primeTheta_div_log_add_integral`: the two exact Abel identities relating
  the roadmap's weighted prime counts,
  `ϑ(x) = π(x) log x - ∫_2^x π(t)/t dt` and `π(x) = ϑ(x)/log x + ∫_2^x ϑ(t)/(t log²t) dt`.
  Both hold for every real cutoff; below `2` all three terms vanish.

## Roadmap role

This is Layer **6.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: Mathlib's exact
finite identity is consumed, not restated, and only the norm-indexed bridges are added.  The two
prime identities are the finite input to Layer 6.2, which turns `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`
by estimating the integrals appearing here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti

open MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Regrouping a weight into its norm fibres -/

/-- The sequence of fibre sums attached to a weight: the total weight of the indices of
`N`-value exactly `n`.  This is the sequence handed to Mathlib's Abel summation. -/
 noncomputable def normFiberSum (w : ι → 𝕜) (n : ℕ) : 𝕜 :=
  ∑ i ∈ normLE N (n : ℝ) with N i = n, w i









/-! ### Abel summation over a Northcott carrier -/







/-! ### Imaginary-power twists -/











/-! ### One-sided bounds for twisted sums -/





/-! ### The ideal and prime carriers of a number field -/

variable (K : Type*) [Field K] [NumberField K]







variable {K}









end TauCeti

end
end


