-- Prove2me | Definitions.Def_KUModComp_lagrangeBasis
-- name    : KUModComp_lagrangeBasis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:39.899835+00:00
-- url     : https://prove2.me/theorems/8c4f2843-736f-4d05-ba91-66414a0da1d6
-- title:
--   Lagrange basis polynomials over a commutative ring
-- statement:
--   Let $R$ be a commutative ring and $\beta_0,\dots,\beta_{K-1} \in R$ (meant: $\beta_i - \beta_j$ a unit for $i \ne j$). The $k$-th Lagrange basis polynomial is
--   $$
--   L_k(X) = \prod_{j \ne k} (\beta_k - \beta_j)^{-1} (X - \beta_j) \in R[X] .
--   $$
--   It has degree at most $K-1$, value $1$ at $\beta_k$ and $0$ at the other $\beta_j$; it is the building block of interpolation at points with unit differences (Figure 1 of the paper).
--
--   **Formalization Note** The inverse is `Ring.inverse`, which is the inverse of a unit and $0$ on a non-unit; under the unit-difference hypothesis only the first case occurs.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Figure 1 (interpolation row) and caption, p. 8

import Mathlib

open Polynomial

namespace KUModComp

variable {R : Type*} [CommRing R]

/-- **Lagrange basis polynomial over a commutative ring.** For points `β 0, …, β (K-1)` in `R`
(meant to have unit pairwise differences, Kedlaya–Umans, Dagstuhl 08381 (2008), Figure 1 caption,
p. 8),
`lagrangeBasis β k = ∏_{j ≠ k} (β k - β j)⁻¹ (X - β j)`.
The inverse is `Ring.inverse`, the inverse of a unit (`0` on non-units, a value never used under
the unit-difference hypothesis). -/
noncomputable def lagrangeBasis {K : ℕ} (β : Fin K → R) (k : Fin K) : R[X] :=
  ∏ j ∈ Finset.univ.erase k, C (Ring.inverse (β k - β j)) * (X - C (β j))

end KUModComp


