-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
-- name    : APSPSource_ThreeSumApsp_Statements_Exponents
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:30.338195+00:00
-- url     : https://prove2.me/theorems/2717e180-846b-475a-a8d7-a7246e42fc54
-- title:
--   Rounding a real polynomial time bound to a step count
-- statement:
--   For real numbers $C,a$ and a natural input size $n$, define the natural-number bound
--
--   $$T_{C,a}(n)=\left\lceil C(n^a+1)\right\rceil_+,$$
--
--   where $\lceil x\rceil_+$ is the least nonnegative integer at least $x$, equivalently the integer ceiling truncated below at zero.
--
--   This definition converts the real-valued bound used in the source's zero-logarithm-exponent time predicate into an integer number of machine steps. It is a bound expression, not an assertion that any program meets it.
--
--   **Formalization Note** At $n=0$, the function uses Lean's total real-power conventions, including when the exponent is negative.
--
--   References:
--
--   1. [Source formalization, lines 52–53](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/Exponents.lean#L52-L53).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/Exponents.lean#L52-L53

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
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
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam



























/-- The bound `C (n^a + 1)` of `SolvedInTimeAt` for `e = 0`, rounded up. -/
noncomputable def stepBound (C a : ℝ) (n : ℕ) : ℕ := ⌈C * ((n : ℝ) ^ a + 1)⌉₊



























end ThreeSumApsp.WordRam


