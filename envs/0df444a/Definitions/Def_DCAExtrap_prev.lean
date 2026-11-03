-- Prove2me | Definitions.Def_DCAExtrap_prev
-- name    : DCAExtrap_prev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:42.846351+00:00
-- url     : https://prove2.me/theorems/40b6a7bf-36c6-4158-a3b7-21a2116cd74f
-- title:
--   Previous iterate $x^{k-1}$ with $x^{-1}=x^0$
-- statement:
--   For a sequence $(x^k)_{k\ge0}$ in $E$, the previous iterate is $x^{k-1}$ for $k\ge1$ and, following the initialization $x^0=x^{-1}$ of Algorithm 1, $x^{-1}:=x^0$ for $k=0$.
--
--   **Formalization Note** Defined by pattern matching: `prev x 0 = x 0` and `prev x (k+1) = x k`.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, Algorithm 1, p.5, Initialization: Choose x0 = x−1

import Mathlib

namespace DCAExtrap

/-- **The previous iterate** `x^{k−1}` (Phan–Le Thi, arXiv:2106.04743v1, Algorithm 1, p.5):
Algorithm 1 is initialised with `x^0 = x^{−1}`, so `prev x 0 = x 0` and `prev x (k+1) = x k`.

**Formalization Note.** The iterates are `x : ℕ → E` with `x k = x^k` for `k ≥ 0`; the
convention `x^{−1} := x^0` is built into this function. -/
def prev {E : Type*} (x : ℕ → E) : ℕ → E
  | 0 => x 0
  | k + 1 => x k

end DCAExtrap


