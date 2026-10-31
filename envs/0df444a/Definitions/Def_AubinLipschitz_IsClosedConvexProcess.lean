-- Prove2me | Definitions.Def_AubinLipschitz_IsClosedConvexProcess
-- name    : AubinLipschitz_IsClosedConvexProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:15.374069+00:00
-- url     : https://prove2.me/theorems/2a9e7d8c-17a6-422d-8536-1dc21fd782b9
-- title:
--   Closed convex process
-- statement:
--   A **closed convex process** from $X$ to $Y$ is a set-valued map whose graph is a closed convex cone in $X\times Y$: the graph is closed, convex, nonempty, and stable under multiplication by every $c>0$.
--
--   Closed convex processes are the set-valued analogues of continuous linear operators, and they satisfy an analogue of the open mapping principle.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), Introduction, p.5

import Mathlib
import Definitions.Def_AubinLipschitz_graphOf

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), Introduction, p.5: a *closed convex process* is a set-valued map whose graph is a
closed convex cone.

**Formalization Note** "Cone" means nonempty and stable under multiplication by positive
scalars; with closedness this puts `(0, 0)` in the graph. -/
def IsClosedConvexProcess {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (G : X → Set Y) : Prop :=
  IsClosed (graphOf G) ∧ Convex ℝ (graphOf G) ∧ (graphOf G).Nonempty ∧
    ∀ c : ℝ, 0 < c → ∀ z ∈ graphOf G, c • z ∈ graphOf G

end AubinLipschitz


