-- Prove2me | Definitions.Def_AnytimeAdaVR_SMState
-- name    : AnytimeAdaVR_SMState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:47.131839+00:00
-- url     : https://prove2.me/theorems/ea231d31-e2fc-4d7b-9a5a-e1d9bd38eef2
-- title:
--   State of an S or M path at a block start
-- statement:
--   The state of an S or M path at the start of a block consists of the starting point $x$, the scale $a$, the block length $b$, the stored point $Y$ of the last failed block, and the number of optimization samples already consumed.
--
--   **Formalization Note** The sample counter is bookkeeping for reading the path's sample stream in order.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 2, p.8; App. C, p.19

import Mathlib

namespace AnytimeAdaVR

/-- **The state of an S or M path at the start of a block.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), Algorithm 2, line 1 and
lines 3–24, p.8, and App. C, p.19 ("Let (x_j, a_j, b_j) be the state at the start of block j"):
the starting point `x`, the scale `a`, the block length `b`, the stored point `Y` of the last
failed block, and `off`, the number of optimization samples consumed by the earlier blocks.

**Formalization Note.** `off` is bookkeeping for reading the path's sample stream in order; it is
not part of the paper's state. -/
structure SMState (d : ℕ) where
  x : EuclideanSpace ℝ (Fin d)
  a : ℝ
  b : ℕ
  Y : EuclideanSpace ℝ (Fin d)
  off : ℕ

end AnytimeAdaVR


