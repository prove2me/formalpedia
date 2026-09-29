-- Prove2me | Definitions.Def_ConeLifts_Factorization_IsConvexBody
-- name    : ConeLifts_Factorization_IsConvexBody
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:29.489239+00:00
-- url     : https://prove2.me/theorems/742f74b0-b8b8-43df-91f3-e5b7b42fb4c4
-- title:
--   Convex body: a compact convex set with the origin in its interior
-- statement:
--   A subset $C \subseteq \mathbb R^n$ is a **convex body** if it is convex, compact, and contains the origin in its interior:
--
--   $$
--   C \text{ convex},\qquad C \text{ compact},\qquad 0 \in \operatorname{int} C .
--   $$
--
--   Gouveia, Parrilo and Thomas assume throughout their paper that every convex set whose cone lifts they study is a convex body. The condition $0 \in \operatorname{int} C$ makes the polar $C^\circ$ compact and gives $(C^\circ)^\circ = C$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. This predicate differs from Mathlib's `ConvexBody` structure (compact, convex, nonempty), which does not ask for the origin to be an interior point.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 (definition of convex body; standing assumption)

import Mathlib

namespace ConeLifts.Factorization

/-- A **convex body** in `ℝⁿ` in the sense of Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and
Cone Factorizations*, arXiv:1111.3164v2, §2, p. 3: a convex set that is compact and contains the
origin in its interior. The paper assumes "throughout" that every convex set whose lifts it studies
is a convex body. `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`.

Not Mathlib's `ConvexBody` (compact, convex, nonempty): here the origin must be an interior point. -/
def IsConvexBody {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C

end ConeLifts.Factorization


