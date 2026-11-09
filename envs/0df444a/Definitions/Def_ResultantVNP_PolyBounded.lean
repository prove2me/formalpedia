-- Prove2me | Definitions.Def_ResultantVNP_PolyBounded
-- name    : ResultantVNP_PolyBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:51.64985+00:00
-- url     : https://prove2.me/theorems/f440c793-fcd4-4453-b884-306af9ee8fde
-- title:
--   Polynomially bounded function $\mathbb N\to\mathbb N$
-- statement:
--   A function $t:\mathbb N\to\mathbb N$ is **polynomially bounded** if there is a constant $c$ with
--
--   $$
--   t(n)\le c\,n^c+c\qquad\text{for all }n .
--   $$
--
--   This is equivalent to being bounded by some polynomial.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib

namespace ResultantVNP

/-- A function `t : ℕ → ℕ` is **polynomially bounded**: `t(n) ≤ c·n^c + c` for some constant `c` and
all `n`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14 ("polynomially bounded in its index n").

**Formalization Note** `c·n^c + c` dominates every polynomial with natural coefficients for a suitable
`c`, and is itself a polynomial, so this is exactly "bounded by some polynomial". -/
def PolyBounded (t : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, t n ≤ c * n ^ c + c

end ResultantVNP


