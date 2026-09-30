-- Prove2me | Definitions.Def_ConeLifts_NonnegRank_IsPolytope
-- name    : ConeLifts_NonnegRank_IsPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:10:00.843332+00:00
-- url     : https://prove2.me/theorems/b918aca8-cac5-4c49-9598-780320c9adee
-- title:
--   Polytope with the origin in its interior
-- statement:
--   A set $C \subseteq \mathbb{R}^n$ is a **polytope** (in the sense used throughout the paper) if
--
--   1. $C = \operatorname{conv}(V)$ is the convex hull of a finite set $V \subseteq \mathbb{R}^n$, and
--   2. the origin lies in the interior of $C$.
--
--   Such a $C$ is a convex body: compact and convex (both automatic for the convex hull of a finite set) with the origin in its interior, which is the paper's standing assumption on every convex set whose lifts it studies. The origin in the interior is also what makes the canonical facet inequalities $h_j(x) \ge 0$ normalizable to $h_j(0) = 1$, so that the slack operator of $C$ is its canonical slack matrix.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The origin in the interior forces $C$ to be full-dimensional; $n = 0$ is allowed ($C = \{0\}$).
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 (convex body, standing assumption); p. 9, §3 (full-dimensional polytope, origin in the interior)

import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.NonnegRank

/-- A **polytope** in the sense of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2: a convex body
(§2, p. 3: compact, convex, with the origin in its interior — the paper's standing assumption
"throughout the paper") that is the convex hull of a finite set of points of `ℝⁿ`
(`EuclideanSpace ℝ (Fin n)`). Compactness and convexity follow from being the convex hull of a finite
set; the origin in the interior is also stated in §3, p. 9 ("we are assuming that the origin is in the
interior of P"). -/
def IsPolytope {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∃ V : Finset (EuclideanSpace ℝ (Fin n)), C = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ∧
    (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C

end ConeLifts.NonnegRank


