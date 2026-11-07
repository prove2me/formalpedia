-- Prove2me | Definitions.Def_IntQuotHNP_XiN
-- name    : IntQuotHNP_XiN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:13.972191+00:00
-- url     : https://prove2.me/theorems/5f755b46-6cb3-4748-a742-938d69995ecf
-- title:
--   Eq. (5) — the integer $k_N$ and the exponent $\xi_N$
-- statement:
--   For a natural number $N$, $k_N$ is the nonnegative integer with $k_N(k_N+1)\le N<(k_N+1)(k_N+2)$, and
--   $$
--   \xi_N=\frac{N+k_N^2-1}{2\bigl(N+k_N(k_N+1)\bigr)} .
--   $$
--   For example $\xi_3=3/10$ and $\xi_6=3/8$. The exponent $\xi_N$ tends to $1/2$ and sets the error range $X\le p^{\xi_N}(\log p)^A$ of Theorem 4.2.
--
--   **Formalization Note** $k_N$ is computed by `Nat.findGreatest` over $\{0,\dots,N\}$; a proved sanity check confirms both defining inequalities.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 4.2, eq. (5), p.22 (PDF p.23)

import Mathlib

namespace IntQuotHNP

/-- **The integer `k_N`** of Theorem 4.2.
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Theorem 4.2, p.22 (PDF p.23): "Let k_N be the nonnegative integer satisfying
k_N(k_N + 1) ≤ N < (k_N + 1)(k_N + 2)".

`kN N` is the largest `k ≤ N` with `k(k + 1) ≤ N`; it satisfies both defining inequalities.

**Formalization Note.** `Nat.findGreatest` searches `k ∈ {0, …, N}`; `k = 0` always qualifies and
any `k` with `k(k + 1) ≤ N` is at most `N`, so the search finds the unique `k` of the paper. -/
def kN (N : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k * (k + 1) ≤ N) N

/-- **The exponent `ξ_N`** of Theorem 4.2, display (5).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 4.2, eq. (5), p.22
(PDF p.23): "ξ_N = (N + k_N² − 1)/(2(N + k_N(k_N + 1)))".

For example `ξ₃ = 3/10`.

**Formalization Note.** Computed in `ℝ` from `kN N`; the denominator is positive for `N ≥ 1`. -/
noncomputable def xiN (N : ℕ) : ℝ :=
  ((N : ℝ) + (kN N : ℝ) ^ 2 - 1) / (2 * ((N : ℝ) + (kN N : ℝ) * ((kN N : ℝ) + 1)))

end IntQuotHNP


