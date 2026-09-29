-- Prove2me | Definitions.Def_ChanPangGQVI_Shared_GQVI
-- name    : ChanPangGQVI_Shared_GQVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:41:46.152517+00:00
-- url     : https://prove2.me/theorems/e5e9c2f3-4ef7-463b-bd68-40874e6947f1
-- title:
--   Solution of the generalized quasi-variational inequality GQVI(K, f)
-- statement:
--   Let $K$ and $f$ be point-to-set mappings of $\mathbb R^n$ into itself, where $\mathbb R^n$ carries the Euclidean inner product $x^T y$. The **generalized quasi-variational inequality problem** $\mathrm{GQVI}(K,f)$ asks for a vector $x$ and a vector $y$ with
--
--   $$
--   x\in K(x),\qquad y\in f(x),\qquad (x'-x)^T y\ \ge\ 0\quad\text{for all } x'\in K(x).
--   $$
--
--   A pair $(x,y)$ with these three properties is a **solution** of $\mathrm{GQVI}(K,f)$. The test points $x'$ range over the whole set $K(x)$, which itself depends on the unknown $x$.
--
--   The GQVI unifies the quasi-variational inequality ($f$ single-valued) and the generalized variational inequality ($K$ constant). When $f$ is a point-to-point mapping, the GQVI is taken with the singleton-valued mapping $x\mapsto\{f(x)\}$: find $x\in K(x)$ with $(x'-x)^T f(x)\ge 0$ for all $x'\in K(x)$.
--
--   This definition is shared by two missions of this series: II, existence via projection (Theorem 5.1, p. 220; Theorem 5.2, p. 220) and III, the projection contraction (Theorem 5.1, p. 220; Theorem 5.3, p. 221).
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)` (Euclidean norm and inner product), point-to-set mappings are functions into `Set`, and the solution predicate is `IsGQVISolution K f x y`.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 212, Section 2 (definition of GQVI(K, f))

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Shared

/-- Chan and Pang, *The generalized quasi-variational inequality problem*, Math. Oper. Res. 7
(1982), p. 212, §2. Given point-to-set mappings `K` and `f` of `ℝⁿ` into itself, a solution of
the generalized quasi-variational inequality problem `GQVI(K, f)` is a pair `(x, y)` with
`x ∈ K(x)`, `y ∈ f(x)` and `(x' - x)ᵀ y ≥ 0` for all `x' ∈ K(x)`. A point-to-point `f` enters
as the singleton-valued mapping `fun z => {f z}`. -/
def IsGQVISolution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K x ∧ y ∈ f x ∧ ∀ x' ∈ K x, 0 ≤ ⟪x' - x, y⟫

end ChanPangGQVI.Shared


