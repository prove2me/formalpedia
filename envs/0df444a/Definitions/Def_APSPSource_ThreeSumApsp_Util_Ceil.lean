-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
-- name    : APSPSource_ThreeSumApsp_Util_Ceil
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:45.160683+00:00
-- url     : https://prove2.me/theorems/4539a143-c3ac-4f02-8941-c5ec8b987812
-- title:
--   The ceiling of the real cube root
-- statement:
--   For a natural number $n$, define
--
--   $$q(n)=\left\lceil n^{1/3}\right\rceil_+.$$
--
--   The power is the real cube root and $\lceil\cdot\rceil_+$ is natural-number ceiling. In particular the definition is meaningful at $n=0$.
--
--   This parameter supplies an integer block size for reductions that use a cube-root scale. Its upper and lower estimates are proved separately.
--
--   References:
--
--   1. [Source formalization, lines 103–104](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Ceil.lean#L103-L104).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Ceil.lean#L103-L104

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/






























/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/











end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/















end Real

namespace ThreeSumApsp

/-- The cube root of `n`, rounded up: `⌈n^{1/3}⌉`. -/
@[expose] noncomputable def cbrtCeil (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊

end ThreeSumApsp


