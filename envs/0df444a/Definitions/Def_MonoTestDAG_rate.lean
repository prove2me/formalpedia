-- Prove2me | Definitions.Def_MonoTestDAG_rate
-- name    : MonoTestDAG_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:27.126627+00:00
-- url     : https://prove2.me/theorems/77e855be-cb09-446a-ace6-37bc208ef094
-- title:
--   The exponent $u(c,d)$
-- statement:
--   For real $c,d$,
--   $$
--   u(c,d):=\min\Bigl\{\tfrac12,\ \tfrac c3,\ \tfrac{c+d}2-1\Bigr\}.
--   $$
--   This is the exponent of the non-adaptive query complexity of monotonicity testing on DAGs with $m=n^{c+o(1)}$ and $\ell=n^{d+o(1)}$.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 1.1, p.1

import Mathlib

namespace MonoTestDAG

/-- The exponent `u(c, d) := min{1/2, c/3, (c + d)/2 − 1}` of Theorem 1.1.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 1.1, p.1. -/
noncomputable def rate (c d : ℝ) : ℝ :=
  min (1 / 2) (min (c / 3) ((c + d) / 2 - 1))

end MonoTestDAG


