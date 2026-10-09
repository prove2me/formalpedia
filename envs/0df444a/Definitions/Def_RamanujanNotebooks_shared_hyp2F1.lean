-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_hyp2F1
-- name    : RamanujanNotebooks_shared_hyp2F1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:22:01.499237+00:00
-- url     : https://prove2.me/theorems/1851a632-f6b7-4b83-a555-accd35930fc9
-- title:
--   Ramanujan's Notebooks, shared: hyp2F1
-- statement:
--   Gauss's hypergeometric series
--   `_2F_1(a, b; c; x) = ∑_{k ≥ 0} (a)_k (b)_k / ((c)_k k!) · x^k` for complex parameters and
--   argument (Part III, (0.2), p. 88, with `p = 2`, `q = 1`; Part II, Chapters 10, 11).
--   Argument order: `hyp2F1 a b c x`.  It is the same series as `hypPFQ [a, b] [c] x`.
--
--   Domain: `c ∉ {0, -1, -2, …}` and `‖x‖ < 1`; also `‖x‖ = 1` when `Re (c - a - b) > 0`
--   (absolute convergence); terminating cases as for `hypPFQ`.
--   Outside: junk as for `hypPFQ`; in particular for `‖x‖ > 1` (non-terminating) the value is
--   `0`, not the analytic continuation.
--   Reference: `_2F_1(1/2, 1/2; 1; 1/2) = √π / Γ(3/4)^2 = 1.1803405990160962260…`,
--   `_2F_1(1/3, 2/3; 1; 1/2) = 1.1595952669639283657…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial

noncomputable section

namespace RamanujanNotebooks

/-- Gauss's hypergeometric series
`_2F_1(a, b; c; x) = ∑_{k ≥ 0} (a)_k (b)_k / ((c)_k k!) · x^k` for complex parameters and
argument (Part III, (0.2), p. 88, with `p = 2`, `q = 1`; Part II, Chapters 10, 11).
Argument order: `hyp2F1 a b c x`.  It is the same series as `hypPFQ [a, b] [c] x`.

Domain: `c ∉ {0, -1, -2, …}` and `‖x‖ < 1`; also `‖x‖ = 1` when `Re (c - a - b) > 0`
(absolute convergence); terminating cases as for `hypPFQ`.
Outside: junk as for `hypPFQ`; in particular for `‖x‖ > 1` (non-terminating) the value is
`0`, not the analytic continuation.
Reference: `_2F_1(1/2, 1/2; 1; 1/2) = √π / Γ(3/4)^2 = 1.1803405990160962260…`,
`_2F_1(1/3, 2/3; 1; 1/2) = 1.1595952669639283657…`. -/
def hyp2F1 (a b c x : ℂ) : ℂ :=
  ∑' k : ℕ, shiftedFactorial a k * shiftedFactorial b k /
    (shiftedFactorial c k * (k.factorial : ℂ)) * x ^ k

end RamanujanNotebooks

end


