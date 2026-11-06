-- Prove2me | Definitions.Def_AnytimeAdaVR_paramStep
-- name    : AnytimeAdaVR_paramStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:29.718795+00:00
-- url     : https://prove2.me/theorems/68d014a7-0f43-47d4-9f68-c2352453dd42
-- title:
--   Table 2 — block parameter update
-- statement:
--   After a block with scale $a$, length $b$ and $m$ large estimates (Table 2), the scale and length are updated by:
--
--   | | S | M |
--   |---|---|---|
--   | scale | $a\leftarrow a+2m/b^2$ | $a\leftarrow a+\sqrt{2/b}\,m/b$ |
--   | success, $m\ge b/2$ | $b\leftarrow\max\{b/2,2\}$ | $b\leftarrow\max\{b/4,2\}$ |
--   | failure, $m<b/2$ | $b\leftarrow 2b$ | $b\leftarrow 4b$ |
--
--   The scale update uses the completed block's length.
--
--   **Formalization Note** The block length is a natural number and success is written $b\le 2m$. All block lengths that occur are $2$, powers of two (S) or $2\cdot4^k$ (M), so the integer divisions are exact whenever the maximum is not $2$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, Table 2, p.7; eq. (36), p.19

import Mathlib
import Definitions.Def_AnytimeAdaVR_SMKind

namespace AnytimeAdaVR

/-- **Table 2: the parameter update after a block.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, p.7, Table 2 ("Parameter
updates after a block with m large estimates"): for S, `a ← a + 2m/b²`, and `b ← max{b/2, 2}` on
success (`m ≥ b/2`), `b ← 2b` on failure (`m < b/2`); for M, `a ← a + √(2/b)·m/b`, and
`b ← max{b/4, 2}` on success, `b ← 4b` on failure. "The scale update uses the completed block's
length." Equivalently (36), p.19.

`paramStep k (a, b) m` is the pair (new scale, new block length) after a block of kind `k` with
scale `a`, length `b` and `m` large estimates.

**Formalization Note.** `b` is a natural number. Success `m ≥ b/2` is written `b ≤ 2m` (exact).
Block lengths are always `2`, or powers of `2` (S), or `2·4^k` (M), so the natural-number
divisions `b/2`, `b/4` are exact whenever the `max` does not return `2`. -/
noncomputable def paramStep : SMKind → ℝ × ℕ → ℕ → ℝ × ℕ
  | .S, (a, b), m =>
      (a + 2 * (m : ℝ) / (b : ℝ) ^ 2, if b ≤ 2 * m then max (b / 2) 2 else 2 * b)
  | .M, (a, b), m =>
      (a + Real.sqrt (2 / (b : ℝ)) * (m : ℝ) / (b : ℝ), if b ≤ 2 * m then max (b / 4) 2 else 4 * b)

end AnytimeAdaVR


