-- Prove2me | Definitions.Def_SilverRateLB_oneSidedHuber
-- name    : SilverRateLB_oneSidedHuber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:11.975431+00:00
-- url     : https://prove2.me/theorems/2add2c49-2de9-4591-a585-2465ec57eba3
-- title:
--   One-sided Huber function $H_\delta$
-- statement:
--   For $\delta>0$ the **one-sided Huber function** is
--   $$H_\delta(z) := \begin{cases}0, & z\le 0,\\ z^2/2, & 0\le z\le\delta,\\ \delta z-\delta^2/2, & z\ge\delta.\end{cases}$$
--   It is convex and $1$-smooth, vanishes on $z\le0$ and has constant slope $\delta$ on $z\ge\delta$. It is the final component of the hard function of Lemma 2.4.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §2.1, p. 6

import Mathlib

namespace SilverRateLB

/-- **One-sided Huber function** `H_δ`:
`H_δ(z) = 0` for `z ≤ 0`, `z²/2` for `0 ≤ z ≤ δ`, `δz − δ²/2` for `z ≥ δ`, with `δ > 0`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §2.1, p. 6:
"A one-sided version of the classical Huber function [Hub64] is defined by Hδ(z) := 0, z ≤ 0;
z²/2, 0 ≤ z ≤ δ; δz − δ²/2, z ≥ δ, δ > 0."

**Formalization Note** The three printed cases agree on the overlaps `z = 0` and `z = δ`; the
definition takes the first applicable case. It is used only with `δ > 0`. -/
noncomputable def oneSidedHuber (δ z : ℝ) : ℝ :=
  if z ≤ 0 then 0 else if z ≤ δ then z ^ 2 / 2 else δ * z - δ ^ 2 / 2

end SilverRateLB


