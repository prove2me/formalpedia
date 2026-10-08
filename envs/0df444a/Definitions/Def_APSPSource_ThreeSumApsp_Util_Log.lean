-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
-- name    : APSPSource_ThreeSumApsp_Util_Log
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:37:01.69215+00:00
-- url     : https://prove2.me/theorems/d73d9fd8-8a83-4385-81a1-31f85a9d5039
-- title:
--   A positive logarithmic factor and elementary domain bounds
-- statement:
--   For a real number $u$, define the clipped logarithmic factor
--
--   $$L(u)=\log(\max\{u,2\}).$$
--
--   This agrees with $\log u$ for $u\ge2$ and takes the value $\log2$ below that threshold. It allows later cost formulas to use a positive logarithmic factor even at small input magnitudes.
--
--   The bundle also supplies the elementary bounds
--
--   $$x\ge3\Rightarrow\log x\ge1,\qquad D\in\mathbb N,\ D\ge16\Rightarrow\sqrt D\ge4,$$
--
--   including the natural-number specialization of the first inequality. These interfaces record the numerical domain facts needed by later parameter and running-time definitions.
--
--   References:
--
--   1. [Source formalization, lines 51–57](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L51-L57).
--   2. [Source formalization, lines 72–74](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L72-L74).
--   3. [Source formalization, lines 101–104](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L101-L104).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L51-L57; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L72-L74; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Log.lean#L101-L104

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/





















/-- `1 ≤ log x` for `x ≥ 3`. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x :=
  (le_log_iff_exp_le (by linarith)).2 (exp_one_lt_three.le.trans hx)

/-- `1 ≤ log n` for a natural number `n ≥ 3`. -/
theorem one_le_log_natCast_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ log n :=
  one_le_log_of_three_le (by exact_mod_cast hn)














/-- `4 ≤ √D` for a natural number `D ≥ 16`. -/
theorem four_le_sqrt_natCast_of_sixteen_le {D : ℕ} (hD : 16 ≤ D) : 4 ≤ √(D : ℝ) :=
  le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)

/-! ### The rounded logarithm `Nat.clog` -/




















end Real

namespace ThreeSumApsp

/-- `log U`, read as `log 2` for `U < 2`, so that a bound with `log U` is positive at `U = 1` as
well. It occurs in the bounds of Theorem 21(b) and in the overhead for copying in
`ConditionalTimes.Claim.RectMinPlusFromSquare`. -/
noncomputable def logU (u : ℝ) : ℝ := Real.log (max u 2)

end ThreeSumApsp


