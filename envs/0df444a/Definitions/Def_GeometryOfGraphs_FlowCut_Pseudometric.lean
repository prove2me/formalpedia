-- Prove2me | Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric
-- name    : GeometryOfGraphs_FlowCut_Pseudometric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:08:07.293916+00:00
-- url     : https://prove2.me/theorems/c8326ee5-296a-4da9-8135-3fd289125f60
-- title:
--   Semi-metric (pseudometric) on a set (Section 2, p. 218, footnote 1)
-- statement:
--   A **semi-metric** (pseudometric) on a set $X$ is a function $d : X \times X \to \mathbb R$ such that for all $x, y, z \in X$
--   $$d(x,x) = 0,\qquad d(x,y) \ge 0,\qquad d(x,y) = d(y,x),\qquad d(x,z) \le d(x,y) + d(y,z).$$
--   Distinct points may be at distance zero. Linial, London and Rabinovich say so explicitly: "Technically, we are discussing semi-metrics, as we allow two distinct points to have distance zero" (p. 218, footnote 1). Every "metric" in the statements of this mission, including the metrics of the LP-duality display and the finite metric spaces of Corollary 3.4, is a semi-metric in this sense.
--
--   **Formalization Note** The predicate is `IsPseudometric d` on a distance function `d : X → X → ℝ` rather than Mathlib's `PseudoMetricSpace` class, so that a statement can quantify over many metrics on the same vertex set. Nonnegativity is listed although it follows from the other three axioms.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 218, Definition 2.1 and footnote 1

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- A (semi-)metric on a set `X`, given as a distance function: `d x x = 0`, `d ≥ 0`, symmetry and the
triangle inequality. Two distinct points may be at distance zero (Linial–London–Rabinovich,
Combinatorica 15 (1995), p. 218, footnote 1: "we are discussing semi-metrics"). -/
def IsPseudometric {X : Type*} (d : X → X → ℝ) : Prop :=
  (∀ x, d x x = 0) ∧ (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = d y x) ∧
    (∀ x y z, d x z ≤ d x y + d y z)

end GeometryOfGraphs.FlowCut


