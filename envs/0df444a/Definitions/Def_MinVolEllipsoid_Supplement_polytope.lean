-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_polytope
-- name    : MinVolEllipsoid_Supplement_polytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:29:45.864115+00:00
-- url     : https://prove2.me/theorems/84ea02e2-6ce6-48be-abeb-1acb405a735f
-- title:
--   The polytope $\mathcal P=\{x\in\mathbb R^K: Sx\le t\}$, display (10)
-- statement:
--   Let $S\in\mathbb R^{J\times K}$ and $t\in\mathbb R^J$. The **polytope** of display (10) is
--
--   $$
--   \mathcal P=\{x\in\mathbb R^K:\ Sx\le t\},
--   $$
--
--   where $Sx\le t$ is meant componentwise: $S_{j:}^\top x\le t_j$ for every row $j\in[J]$, with $S_{j:}\in\mathbb R^K$ the transpose of the $j$-th row of $S$.
--
--   This is the class of sets for which §3 of the paper develops its tractable semidefinite approximations (Theorems 2 and 3) and for which Appendix B.1 sets up the scaled maximum volume inscribed ellipsoid.
--
--   **Formalization Note** The dimension $K$ is written $n$ and the number of rows $J$ is $m$. No boundedness or interior condition is built in; the theorems that need Assumption 1 (compact, convex, full-dimensional) state it as hypotheses.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, §3, display (10), p.10; Appendix B.1, p.31

import Mathlib

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The polytope `𝒫 = {x ∈ ℝᴷ : Sx ≤ t}`** (Mittal & Hanasusanto, *Finding Minimum Volume
Circumscribing Ellipsoids Using Generalized Copositive Programming*, arXiv:1807.07507v4, §3,
display (10), p.10; also Appendix B.1, p.31).

For `S ∈ ℝ^{J×K}` and `t ∈ ℝᴶ`, `polytope S t` is the set of `x ∈ ℝᴷ` with `Sx ≤ t`
componentwise, i.e. `S_{j:}⊤ x ≤ t_j` for every row `j ∈ [J]`.

**Formalization Note** The dimension is written `n` (the paper's `K`) and the number of rows `m`
(the paper's `J`). `Sx ≤ t` is the pointwise order on `Fin m → ℝ`. No boundedness or
full-dimensionality is bundled: the statements that need Assumption 1 state it. -/
def polytope {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | S *ᵥ x ≤ t}

end MinVolEllipsoid.Supplement


