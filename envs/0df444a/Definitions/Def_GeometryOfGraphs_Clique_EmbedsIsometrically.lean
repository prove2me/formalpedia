-- Prove2me | Definitions.Def_GeometryOfGraphs_Clique_EmbedsIsometrically
-- name    : GeometryOfGraphs_Clique_EmbedsIsometrically
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:47.61304+00:00
-- url     : https://prove2.me/theorems/f83a814a-a170-4c76-acbc-24401422ae25
-- title:
--   Isometric embedding into a real normed space of given dimension
-- statement:
--   Let $X$ carry a distance function $\delta$, and let $d$ be a nonnegative integer. The space $X$ **embeds isometrically in dimension $d$** when there are a norm $N$ on $\mathbb R^d$ and a map $\varphi:X\to\mathbb R^d$ satisfying
--
--   $$
--   N\bigl(\varphi(x)-\varphi(y)\bigr)=\delta(x,y)\qquad\text{for every }x,y\in X.
--   $$
--
--   This is the distance-preserving case of the paper's embedding definition. The norm is allowed to vary with the realization, as required by metric dimension.
--
--   **Formalization Note** The source's finite metric spaces may be pseudometric: distinct points can have distance zero. The definition accepts a distance function; mission theorems supply the relevant metric assumptions.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 218–219, isometry and Definition 2.1

import Definitions.Def_GeometryOfGraphs_Clique_IsNormFun

namespace GeometryOfGraphs.Clique

/-- Isometric realization in a real normed coordinate space of dimension `d`. -/
def EmbedsIsometrically {X : Type*} (d : ℕ) (δ : X → X → ℝ) : Prop :=
  ∃ N : (Fin d → ℝ) → ℝ, IsNormFun N ∧
    ∃ φ : X → (Fin d → ℝ), ∀ x y, N (φ x - φ y) = δ x y

end GeometryOfGraphs.Clique


