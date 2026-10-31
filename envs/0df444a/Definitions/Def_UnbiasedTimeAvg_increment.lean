-- Prove2me | Definitions.Def_UnbiasedTimeAvg_increment
-- name    : UnbiasedTimeAvg_increment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:38.074821+00:00
-- url     : https://prove2.me/theorems/1265940e-b2fc-44e8-bcc2-ba7f0c40a910
-- title:
--   The increments $Y_l-Y_{l-1}$ with $Y_{-1}=0$
-- statement:
--   For a sequence of random variables $(Y_l)_{l\ge0}$, with the convention $Y_{-1}:=0$, the increment at level $l$ is $Y_l-Y_{l-1}$: it equals $Y_0$ for $l=0$ and $Y_l-Y_{l-1}$ for $l\ge1$. It is the summand of the single term estimator of Theorem 3.1.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Theorem 3.1, p.7; Appendix F, p.28

import Mathlib

namespace UnbiasedTimeAvg

/-- **The increments `Y_l − Y_{l−1}` with `Y_{−1} := 0`.** Kahalé, arXiv:2209.09581v1,
Theorem 3.1, p.7 ("Set `Z := (Y_N − Y_{N−1})/p_N`, with `Y_{−1} := 0`") and p.28.

`increment Y 0 = Y_0` and `increment Y (l + 1) = Y_{l+1} − Y_l`. -/
def increment {Ω : Type*} (Y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Y 0
  | l + 1 => fun ω => Y (l + 1) ω - Y l ω

end UnbiasedTimeAvg


