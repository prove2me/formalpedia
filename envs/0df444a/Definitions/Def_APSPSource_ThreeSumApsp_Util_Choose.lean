-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Choose
-- name    : APSPSource_ThreeSumApsp_Util_Choose
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:46.267867+00:00
-- url     : https://prove2.me/theorems/07f8f7ba-b435-46d5-8474-4174aee9e689
-- title:
--   A term in a binomial expansion
-- statement:
--   For natural numbers $n,k,j$, define
--
--   $$M(n,k,j)=\binom nj\,k^j\,(n\mathbin{\dot-}k)^{n\mathbin{\dot-}j},$$
--
--   where $a\mathbin{\dot-}b=\max\{a-b,0\}$. For $k,j\le n$, this is term $j$ in the binomial expansion of $(k+(n-k))^n=n^n$.
--
--   This nonnegative integer expression is used in the later comparison of binomial terms and combinatorial estimates. The definition alone does not assert where the maximum occurs.
--
--   References:
--
--   1. [Source formalization, lines 69–70](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Choose.lean#L69-L70).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Choose.lean#L69-L70

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Binomial coefficients

Upper bounds. A single summand of the binomial expansion of `(a + b) ^ n` is at most the whole sum
(`Nat.choose_mul_pow_mul_pow_le`); with `a = 1` this is `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`
(`Nat.choose_mul_pow_le`), which the paper uses with `b = 9`. And `binom(n, k) ≤ (e n / k) ^ k`
(`Nat.choose_le_exp_mul_div_pow`).

A lower bound. For `k ≤ n`, the largest of the `n + 1` terms `binom(n, j) k^j (n-k)^{n-j}` of the
expansion of `n^n = (k + (n-k))^n` is the one with `j = k`: the terms increase up to `j = k` and
decrease from there on. This gives the standard lower bound on a binomial coefficient
(`Nat.pow_self_le_mul_choose_mul_pow_mul_pow`), which Section 4.4 uses in the proof of Corollary 26
and, written with the entropy function as `e^{n H(k/n)}/(n+1) ≤ binom(n, k)`, in the proof of
Corollary 31.
-/

public section

namespace Nat

/-! ## Upper bounds -/

































/-! ## The largest term of a binomial expansion -/

/-- The term number `j` of the expansion of `n^n = (k + (n-k))^n`. -/
 def modeTerm (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)





















































end Nat


