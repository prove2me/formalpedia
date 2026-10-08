-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
-- name    : APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:37.657227+00:00
-- url     : https://prove2.me/theorems/490357b0-3d9c-4acc-862f-0e8c45cecdbe
-- title:
--   Parameters for the arithmetic of repeated squaring
-- statement:
--   The record used in the repeated-squaring cost calculation stores
--
--   $$s=(n,V,W)\in\mathbb N\times\mathbb R\times\mathbb R.$$
--
--   The intended interpretation is that $n$ is the number of vertices, $V$ stands for a running-time quantity $T(\lceil n^{1/3}\rceil)$, and $W$ stands for a logarithmic magnitude factor $\log U$ when matrix entries are bounded by $U$.
--
--   The record imposes no positivity conditions and no equations linking its fields to an actual algorithm. It provides named parameters for the subsequent arithmetic estimates and time-claim definitions.
--
--   References:
--
--   1. [Source formalization, lines 124–131](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L124-L131).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L124-L131

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
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
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/




























/-! ## Theorem 21(b): the (min,+)-product -/
























































/-! ## Theorem 21(b): APSP -/

/-- The quantities in the arithmetic of repeated squaring. -/
 structure Squaring where
  /-- The number of vertices. -/
  n : ℕ
  /-- Stands for the time `T(⌈n^{1/3}⌉)`. -/
  V : ℝ
  /-- Stands for `log U`, where `U` bounds the entries. -/
  W : ℝ






























































/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/


























































































/-! ## Theorem 22 -/









end ThreeSumApsp


