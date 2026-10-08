-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
-- name    : APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:45.497927+00:00
-- url     : https://prove2.me/theorems/ea7d259c-0fd0-4ae4-89f0-3c9c720de9c1
-- title:
--   Eventual polynomial and polylogarithmic upper bounds
-- statement:
--   For a function $f:\mathbb N\to\mathbb R$ and real exponent $a$, define the two eventual upper-bound predicates
--
--   $$\operatorname{UpperPow}(f,a)\iff\exists C\in\mathbb R,\ \forall\text{ sufficiently large }n,\ f(n)\le Cn^a,$$
--   $$\operatorname{UpperPolylog}(f,a)\iff\exists C\in\mathbb R\ \exists e\in\mathbb N,\ \forall\text{ sufficiently large }n,\ f(n)\le Cn^a(\log n)^e.$$
--
--   These definitions bound $f$ itself, rather than $|f|$, and do not impose a sign condition on the existential constant $C$. Their intended use is to state upper estimates for nonnegative costs. Later lemmas connect such estimates to the corresponding standard asymptotic predicates when the required hypotheses hold.
--
--   References:
--
--   1. [Source formalization, lines 34–40](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L34-L40).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L34-L40

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- `f(n) = O(n^a)`, as an upper bound. -/
def UpperBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * (n : ℝ) ^ a

/-- `f(n) = O(n^a (log n)^{O(1)})`, as an upper bound. -/
def UpperPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ (C : ℝ) (e : ℕ), ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)







variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/











namespace UpperPowPolylog






















































end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp


