-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_hyp2F1R
-- name    : RamanujanNotebooks_shared_hyp2F1R
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:21:46.089299+00:00
-- url     : https://prove2.me/theorems/fb3daccb-e900-4143-8c2c-3519df5cadeb
-- title:
--   Ramanujan's Notebooks, shared: hyp2F1R
-- statement:
--   Gauss's hypergeometric series `_2F_1(a, b; c; x)` for REAL parameters and real
--   argument, with real value; the same series as `hyp2F1` (Part III, (0.2), p. 88).
--
--   Domain: `c ∉ {0, -1, -2, …}` and `|x| < 1`; also `x = 1` when `c - a - b > 0` and `x = -1`
--   when `c - a - b > 0`; terminating cases as for `hypPFQ`.
--   Outside: non-summable family, value `0` (e.g. `a = b = 1/2`, `c = 1` at `x = 1` and at
--   `x = -1`).
--   Reference: `hyp2F1R (1/2) (1/2) 1 x = (2/π) K(√x)` for `0 ≤ x < 1`;
--   `hyp2F1R (-1/2) (1/2) 1 x = (2/π) E(√x)`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

noncomputable section

namespace RamanujanNotebooks

/-- Gauss's hypergeometric series `_2F_1(a, b; c; x)` for REAL parameters and real
argument, with real value; the same series as `hyp2F1` (Part III, (0.2), p. 88).

Domain: `c ∉ {0, -1, -2, …}` and `|x| < 1`; also `x = 1` when `c - a - b > 0` and `x = -1`
when `c - a - b > 0`; terminating cases as for `hypPFQ`.
Outside: non-summable family, value `0` (e.g. `a = b = 1/2`, `c = 1` at `x = 1` and at
`x = -1`).
Reference: `hyp2F1R (1/2) (1/2) 1 x = (2/π) K(√x)` for `0 ≤ x < 1`;
`hyp2F1R (-1/2) (1/2) 1 x = (2/π) E(√x)`. -/
def hyp2F1R (a b c x : ℝ) : ℝ :=
  ∑' k : ℕ, shiftedFactorialR a k * shiftedFactorialR b k /
    (shiftedFactorialR c k * (k.factorial : ℝ)) * x ^ k

end RamanujanNotebooks

end


