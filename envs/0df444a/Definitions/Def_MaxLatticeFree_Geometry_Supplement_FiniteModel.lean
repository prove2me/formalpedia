-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_Supplement_FiniteModel
-- name    : MaxLatticeFree_Geometry_Supplement_FiniteModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:59:14.706709+00:00
-- url     : https://prove2.me/theorems/028eb16b-5830-4a8c-818f-00804e339e42
-- title:
--   The finite relaxation $R_f(r^1,\dots,r^m)$
-- statement:
--   Let $f\in\mathbb R^q$ and $r^1,\dots,r^m\in\mathbb R^q$. The **finite relaxation** $R_f(r^1,\dots,r^m)$ is the set of $s\in\mathbb R^m$ satisfying
--
--   $$
--   f+\sum_{j=1}^m r^js_j\in\mathbb Z^q,\qquad s\ge0 .
--   $$
--
--   It arises from $q$ rows of an optimal simplex tableau after dropping the nonnegativity of the basic variables and the integrality of the nonbasic ones. The data $f,r^j$ may be irrational.
--
--   **Formalization Note** All $m$ coordinates are required to be nonnegative.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, pp. 3–4, (1) and the definition of $R_f(r^1,\dots,r^k)$

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel

namespace MaxLatticeFree.Geometry.Supplement

open MaxLatticeFree.Inequalities

/-- The finite relaxation `R_f(r¹, …, rᵐ)` (arXiv:1701.06543v1, pp. 3–4, (1)): the vectors
`s ∈ ℝᵐ` with `s ≥ 0` and `f + ∑_j r^j s_j ∈ ℤ^q`. The data `f, r^j` may be irrational. -/
noncomputable def RfFinite {q m : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (r : Fin m → EuclideanSpace ℝ (Fin q)) : Set (Fin m → ℝ) :=
  {s | (∀ j, 0 ≤ s j) ∧ f + ∑ j, s j • r j ∈ integralPoints q}

end MaxLatticeFree.Geometry.Supplement


