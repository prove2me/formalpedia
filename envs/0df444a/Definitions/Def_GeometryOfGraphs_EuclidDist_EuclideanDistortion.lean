-- Prove2me | Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion
-- name    : GeometryOfGraphs_EuclidDist_EuclideanDistortion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:14.496902+00:00
-- url     : https://prove2.me/theorems/85902e04-ddb7-4dea-9686-40a1236b6e68
-- title:
--   Semi-metrics and embeddings into Euclidean space with distortion ≤ c (Definition 2.1, p. 218)
-- statement:
--   Let $X$ be a set and $d : X \times X \to \mathbb{R}$. We call $d$ a **semi-metric** (pseudometric) if for all $x, y, z \in X$
--
--   1. $d(x,y) \ge 0$,
--   2. $d(x,x) = 0$,
--   3. $d(x,y) = d(y,x)$,
--   4. $d(x,z) \le d(x,y) + d(y,z)$.
--
--   Distinct points may be at distance $0$; the paper allows this explicitly (p. 218, footnote 1: "Technically, we are discussing semi-metrics, as we allow two distinct points to have distance zero").
--
--   For $c \in \mathbb{R}$, the space $(X,d)$ **embeds in a Euclidean space with distortion at most $c$** if there are a dimension $m \in \mathbb{N}$ and a map $\varphi : X \to \mathbb{R}^m$ such that, with $\|\cdot\|$ the Euclidean norm,
--
--   $$
--   \|\varphi(x) - \varphi(y)\| \;\le\; d(x,y) \;\le\; c\,\|\varphi(x) - \varphi(y)\| \qquad \text{for all } x, y \in X .
--   $$
--
--   This is Definition 2.1 of Linial, London and Rabinovich (pp. 218–219), specialised to Euclidean target spaces: the inequality $d(x_1,x_2) \ge \|\varphi(x_1)-\varphi(x_2)\| \ge \frac1c d(x_1,x_2)$ of the page, multiplied through by $c$. It is the notion of distortion used in Corollary 3.5 (p. 224), where "a Euclidean space" may have any finite dimension.
--
--   **Formalization Note** The semi-metric is a function `d : X → X → ℝ` with the four axioms as an explicit predicate `IsPseudometric`. The Euclidean space is `EuclideanSpace ℝ (Fin m)` with an existentially quantified dimension `m`; for a finite $X$ any embedding spans at most $|X|-1$ dimensions, so this loses nothing. Both inequalities are kept; the map is contractive, as on the page. The equivalent expanding form $d \le \|\psi(x)-\psi(y)\| \le c\,d$ is obtained with $\psi = c\varphi$ when $c > 0$.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 218–219, Definition 2.1 and footnote 1; p. 224, Corollary 3.5

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric

namespace GeometryOfGraphs.EuclidDist

/-- `(X, d)` embeds in a Euclidean space with distortion at most `c` (Definition 2.1, p. 218):
there are a dimension `m` and a map `φ : X → ℝ^m` (Euclidean norm) with
`‖φ x - φ y‖ ≤ d x y ≤ c * ‖φ x - φ y‖` for all `x, y`. -/
def EmbedsEuclidean {X : Type*} (d : X → X → ℝ) (c : ℝ) : Prop :=
  ∃ (m : ℕ) (φ : X → EuclideanSpace ℝ (Fin m)),
    ∀ x y, ‖φ x - φ y‖ ≤ d x y ∧ d x y ≤ c * ‖φ x - φ y‖

end GeometryOfGraphs.EuclidDist


