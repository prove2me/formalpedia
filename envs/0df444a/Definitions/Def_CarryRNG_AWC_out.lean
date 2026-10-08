-- Prove2me | Definitions.Def_CarryRNG_AWC_out
-- name    : CarryRNG_AWC_out
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:07.230739+00:00
-- url     : https://prove2.me/theorems/5f96227b-0e19-461f-b58d-762019209035
-- title:
--   The generated digit sequence $x_1, x_2, x_3, \dots$ of a seed (Sections 2 and 4.2)
-- statement:
--   Let $f$ be the add-with-carry map for base $b$ and lags $0 < s < r$, and let $x = (x_1, \dots, x_r, c)$ be a seed. The **generated digit sequence** of $x$ is
--
--   $$x_1, x_2, \dots, x_r, x_{r+1}, x_{r+2}, \dots,$$
--
--   where $x_1, \dots, x_r$ are the seed digits and, for $j \ge 1$, $x_{r+j}$ is the last digit of the state $f^j(x)$. Equivalently, the state $f^j(x)$ is $(x_{j+1}, \dots, x_{j+r}, c_j)$ for some carry $c_j$, and the digits satisfy $x_n = x_{n-r} + x_{n-s} + c \bmod b$ (Section 4.2). For example, with $b = 10$, $r = 2$, $s = 1$ and seed $(1, 2, 0)$ the sequence is $1, 2, 3, 5, 8, 3, 2, 6, 8, 4, 3, 8, \dots$ (p. 468).
--
--   **Formalization Note** `out b L x n` is $x_n$ with one-based $n$: the seed digit at Lean index $n - 1$ when $1 \le n \le r$, and the digit at Lean index $r - 1$ of $f^{\,n-r}(x)$ when $n > r$. The value at $n = 0$ is a junk value (the seed digit $x_r$) and is never used.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 465, Section 2; p. 467, Section 4.2 (x_n = x_{n-r} + x_{n-s} + c mod b); p. 468 (example sequence)

import Definitions.Def_CarryRNG_AWC_step

namespace CarryRNG.AWC

/-- The generated digit sequence `x_1, x_2, …` of a seed, one-based: `out b L z n` is the seed
digit `x_n` for `1 ≤ n ≤ r`, and for `n > r` it is `x_n`, the last digit of `f^(n-r)(z)`.
The value at `n = 0` is a junk value (the last digit of `f^0(z)` = `x_r`) and is never used. -/
def out (b : ℕ) (L : Lags) (z : State b L.r) (n : ℕ) : ℕ :=
  if h : 1 ≤ n ∧ n ≤ L.r then (z.x ⟨n - 1, by omega⟩).val
  else (((step b L)^[n - L.r] z).x ⟨L.r - 1, by have := L.hsr; omega⟩).val

end CarryRNG.AWC


