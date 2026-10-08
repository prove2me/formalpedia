-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
-- name    : APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:47.400332+00:00
-- url     : https://prove2.me/theorems/6b416aaf-7fee-46d4-a313-98110d020897
-- title:
--   Size and weight parameters for a uniform Exact Triangle time shape
-- statement:
--   A size-bound record contains a natural number $s$ of vertices per part and a real weight-bound parameter $u$. For a real saving exponent $\delta$ and natural logarithm exponent $e$, define
--
--   $$F_{\delta,e}(s,u)=s^{3-\delta}(\log s+1)^e\bigl(1+\log(\max\{u,2\})\bigr)^2.$$
--
--   This is the source's uniform running-time shape without its multiplicative constant. The record itself imposes no positivity assumptions on $u$, and the function uses total real-power conventions at $s=0$.
--
--   The definition separates the parameter-dependent shape from the constant supplied in later Exact Triangle time claims.
--
--   References:
--
--   1. [Source formalization, lines 167–176](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean#L167-L176).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean#L167-L176

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp



























































































/-! ## The bounds as printed -/





































/-! ## A bound for all sizes and all bounds on the weights -/

/-- The number `s` of vertices per part and the bound `u` on the weights. -/
structure SizeBound where
  /-- The number of vertices per part. -/
  s : ℕ
  /-- The bound on the absolute values of the weights. -/
  u : ℝ

/-- The time `uniformTime` without its constant: `s^{3-δ} (log s + 1)^e (1 + log u)²`. -/
 noncomputable abbrev uniformShape (δ : ℝ) (e : ℕ) (p : SizeBound) : ℝ :=
  (p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2































































































end ThreeSumApsp


