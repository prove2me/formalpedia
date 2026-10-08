-- Prove2me | Definitions.Def_ErrBoundCplx_ISTA_Hoffman
-- name    : ErrBoundCplx_ISTA_Hoffman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:31.206405+00:00
-- url     : https://prove2.me/theorems/83fc49e7-bc7d-4655-aafa-2e96922a6a76
-- title:
--   Definition 1: polyhedra X = {Ax ≤ a}, Y = {Ex = e} and Hoffman constants of a pair (A, E)
-- statement:
--   Let $A$ be a real matrix with rows indexed by a finite set $I$ and columns by a finite set $K$, and $E$ a real matrix with rows indexed by a finite set $P$ and the same columns. For right-hand sides $a \in \mathbb R^I$ and $e \in \mathbb R^P$ consider the polyhedra
--   $$X = \{x \in \mathbb R^K : Ax \le a\}, \qquad Y = \{x \in \mathbb R^K : Ex = e\}.$$
--   A number $\nu \ge 0$ is a **Hoffman constant for the pair $(A, E)$** if, for every $(a, e)$ with $X \cap Y \neq \emptyset$,
--   $$\operatorname{dist}(x, X \cap Y) \le \nu\,\|Ex - e\| \qquad \text{for all } x \in X. \qquad (5)$$
--   Distances and norms are Euclidean. Hoffman's theorem says such a constant exists; the paper uses it, through a result of Beck and Shtern, to obtain an explicit error bound for the $\ell_1$-regularized least squares objective (Lemma 10).
--
--   **Formalization Note** "$\nu = \nu(A, E)$ only depends on the pair $(A, E)$" is encoded by quantifying over all right-hand sides $(a, e)$. Vectors live in `EuclideanSpace ℝ K`, matrices act by `Matrix.toEuclideanLin`, and $Ax \le a$ is componentwise. Index sets are arbitrary finite types, so that the $(2^n + 1)$-row matrix of Lemma 10 can be indexed naturally. The page's "$E = \mathbb R^{r\times n}$" is read as $E \in \mathbb R^{r \times n}$.
-- source:
--   arXiv:1510.08234v3, §3.2.1, Definition 1, p. 10, (5)

import Mathlib

namespace ErrBoundCplx.ISTA

/-- Definition 1, p. 10: the polyhedron `X = {x : Ax ≤ a}` (componentwise order), for a matrix
`A` with rows indexed by `ι` and columns by `κ`, acting on `ℝ^κ = EuclideanSpace ℝ κ`. -/
def polyX {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (a : EuclideanSpace ℝ ι) : Set (EuclideanSpace ℝ κ) :=
  {x | ∀ i, Matrix.toEuclideanLin A x i ≤ a i}

/-- Definition 1, p. 10: the affine set `Y = {x : Ex = e}`. -/
def polyY {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (E : Matrix ρ κ ℝ) (e : EuclideanSpace ℝ ρ) : Set (EuclideanSpace ℝ κ) :=
  {x | Matrix.toEuclideanLin E x = e}

/-- Definition 1 (Hoffman's error bound), p. 10: `ν ≥ 0` is a Hoffman constant for the pair
`(A, E)` if, for **every** right-hand side `(a, e)` with `X ∩ Y ≠ ∅`,
`dist(x, X ∩ Y) ≤ ν ‖Ex − e‖` for all `x ∈ X` (5). Distances and norms are Euclidean.
Quantifying over all `(a, e)` is what "ν = ν(A, E) only depends on the pair (A, E)" means. -/
def IsHoffmanConst {ι ρ κ : Type*} [Fintype ι] [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (E : Matrix ρ κ ℝ) (ν : ℝ) : Prop :=
  0 ≤ ν ∧ ∀ (a : EuclideanSpace ℝ ι) (e : EuclideanSpace ℝ ρ),
    (polyX A a ∩ polyY E e).Nonempty → ∀ x ∈ polyX A a,
      Metric.infDist x (polyX A a ∩ polyY E e) ≤ ν * ‖Matrix.toEuclideanLin E x - e‖

end ErrBoundCplx.ISTA


