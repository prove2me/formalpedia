-- Prove2me | Definitions.Def_ResultantVNP_PolyFamily
-- name    : ResultantVNP_PolyFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:56.403097+00:00
-- url     : https://prove2.me/theorems/9a1c17e7-f482-4dea-808b-1cfa6c488020
-- title:
--   Polynomial family $(p_n)_n$ over $\mathbb C$
-- statement:
--   A **polynomial family** $(p_n)_{n\in\mathbb N}$ over $\mathbb C$ consists, for each index $n$, of a number of variables $v(n)$ and a polynomial $p_n\in\mathbb C[x_1,\dots,x_{v(n)}]$.
--
--   Valiant's classes VP and VNP are sets of polynomial families.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib

namespace ResultantVNP

/-- A **polynomial family** `(p_n)_n` over `ℂ`: for each index `n`, a number of variables `nvars n`
and a polynomial `p_n ∈ ℂ[x₁, …, x_{nvars n}]`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14 ("A polynomial family (p_n)_n").

**Formalization Note** Variables are `Fin (nvars n)` (0-based). -/
structure PolyFamily where
  /-- The number of variables of `p_n`. -/
  nvars : ℕ → ℕ
  /-- The polynomial `p_n`. -/
  p : ∀ n, MvPolynomial (Fin (nvars n)) ℂ

end ResultantVNP


