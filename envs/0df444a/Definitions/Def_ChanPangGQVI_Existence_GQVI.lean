-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_GQVI
-- name    : ChanPangGQVI_Existence_GQVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:35:51.043819+00:00
-- url     : https://prove2.me/theorems/840610cb-0ea9-4b6b-adae-b1965ea79f8d
-- title:
--   Solution of the generalized quasi-variational inequality GQVI(K, f), and the shifted map μ + q
-- statement:
--   Let $K$ and $f$ be point-to-set mappings of $\mathbb R^n$ into itself, where $\mathbb R^n$ carries the Euclidean inner product $x^T y$. The **generalized quasi-variational inequality problem** $\mathrm{GQVI}(K,f)$ asks for a vector $x$ and a vector $y$ with
--
--   $$
--   x\in K(x),\qquad y\in f(x),\qquad (x'-x)^T y\ \ge\ 0\quad\text{for all } x'\in K(x).
--   $$
--
--   A pair $(x,y)$ with these three properties is called a solution of $\mathrm{GQVI}(K,f)$. Note that the test points $x'$ range over the whole set $K(x)$.
--
--   The file also defines, for a point-to-set mapping $\mu$ and a vector $q$, the mapping $\mu+q$ given by $(\mu+q)(x)=\{y+q : y\in\mu(x)\}$, which appears in the existence theorems of §4 as the GQVI$(K,\mu+q)$.
--
--   The GQVI contains the variational inequality ($K$ constant, $f$ single-valued), the quasi-variational inequality ($f$ single-valued), and the generalized variational inequality ($K$ constant) as special cases.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)` (Euclidean norm), point-to-set mappings are functions into `Set`, and the solution predicate is `IsGQVISolution K f x y`; the shifted map is `shiftMap μ q`.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 212, Section 2 (definition of GQVI(K, f)); p. 217, Theorem 4.1 (the map μ + q)

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang, *The generalized quasi-variational inequality problem*, Math. Oper. Res. 7
(1982), p. 212, §2. Given point-to-set mappings `K` and `f` of `ℝⁿ` into itself, a solution of
the generalized quasi-variational inequality problem `GQVI(K, f)` is a pair `(x, y)` with
`x ∈ K(x)`, `y ∈ f(x)` and `(x' - x)ᵀ y ≥ 0` for all `x' ∈ K(x)`. -/
def IsGQVISolution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K x ∧ y ∈ f x ∧ ∀ x' ∈ K x, 0 ≤ ⟪x' - x, y⟫

/-- The point-to-set mapping `μ + q : x ↦ {y + q : y ∈ μ(x)}` (Chan and Pang 1982, §4, p. 217,
Theorem 4.1: "the GQVI(K, μ + q)"). -/
def shiftMap {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (q : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)) :=
  fun x => (fun y => y + q) '' μ x

end ChanPangGQVI.Existence


