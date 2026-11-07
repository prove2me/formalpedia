-- Prove2me | Definitions.Def_MatSemiBurnside_F
-- name    : MatSemiBurnside_F
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:22.139115+00:00
-- url     : https://prove2.me/theorems/18234e26-d322-4639-909a-343fdb3543b7
-- title:
--   The bound $F_d(N,m)$
-- statement:
--   For positive integers $N,d,m$,
--   $$F_d(N,m) := \big[m(N+1)^2\big]^{(2^{d+3}+1)^{d-1}}.$$
--
--   For fixed $d$ this is polynomial in $m$ and $N$; as a function of $d$ it is $(m(N+1))^{2^{O(d^2)}}$. Theorem 1 bounds both the cardinality and the diameter of the quotient by $F_d(N,|X|)$.
--
--   **Formalization Note** Computed in $\mathbb N$; for $d\ge1$ the truncated subtraction $d-1$ is the true one. For example $F_1(N,m)=m(N+1)^2$.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), eq. (1), p.7 (also p.3)

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside

/-- **The bound F_d(N, m).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), eq. (1), p.7 (also p.3): "For positive integers N, d, m, define
Fd(N, m) := [m(N + 1)²]^((2^(d+3)+1)^(d−1))."

**Formalization Note.** Computed in ℕ. `d - 1` is truncated subtraction; it is the true d − 1
for the positive d of the source. -/
def F (d N m : ℕ) : ℕ :=
  (m * (N + 1) ^ 2) ^ ((2 ^ (d + 3) + 1) ^ (d - 1))

end MatSemiBurnside


