-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:17.811172+00:00
-- url     : https://prove2.me/theorems/5051d398-52bc-453a-bf85-4e407ec7f07d
-- title:
--   Clearing low bits after an integer offset
-- statement:
--   For integers $U,c$ and a natural number $t$, define
--
--   $$B(U,t,c)=-2U+2^t\left\lfloor\frac{\max\{c+2U,0\}}{2^t}\right\rfloor.$$
--
--   The maximum reflects conversion of the shifted integer to a natural number. On the intended domain $c+2U\ge0$, the operation adds $2U$, clears the lowest $t$ binary bits, and subtracts $2U$ again.
--
--   This total arithmetic function specifies the lower approximation maintained by the later bit-search routine; its iteration and correctness properties are proved separately.
--
--   References:
--
--   1. [Source formalization, lines 41–42](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/BitSearch.lean#L41-L42).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/BitSearch.lean#L41-L42

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The entries of a (min,+)-product, found bit by bit

Theorem 21(b), after [VW18, Theorem 4.2]: the (min,+)-product is computed
by a binary search for all entries at once.  An entry `c` with `-2U ≤ c ≤ 2U` is approached from
below: `bitLo U t c` is `c` with the lowest `t` bits of `c + 2U` cleared.

* The search starts at `t = R`, where `4U < 2^R`, with `-2U` (`bitLo_top`), and it ends at `t = 0`
  with `c` (`bitLo_zero`).
* One round goes from `t + 1` to `t`: it asks whether `c < bitLo U (t + 1) c + 2^t` and adds `2^t`
  if not (`bitLo_step`).
* The question is whether the pair `(i, j)` has a witness: `c` is below a number exactly if one of
  the sums `A[i,k] + B[k,j]` is (`exists_sum_lt_iff`).  So one round for all entries is one call of
  a routine that finds all pairs with a witness.
-/

@[expose] public section

namespace ThreeSumApsp.Spec











/-- `c` with the lowest `t` bits of `c + 2U` cleared. -/
def bitLo (U : ℤ) (t : ℕ) (c : ℤ) : ℤ := -(2 * U) + (((c + 2 * U).toNat / 2 ^ t * 2 ^ t : ℕ) : ℤ)































































end ThreeSumApsp.Spec


