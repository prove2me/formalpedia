-- Prove2me | Definitions.Def_AubinLipschitz_contingentDeriv
-- name    : AubinLipschitz_contingentDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:01.662842+00:00
-- url     : https://prove2.me/theorems/9c6a273b-646d-49f8-8c87-36a660e4ea10
-- title:
--   §2, (1) — the contingent derivative $DF(x_0,y_0)$
-- statement:
--   Let $F$ be a set-valued map between normed spaces $X$ and $Y$, and $(x_0,y_0)$ a point. The **contingent derivative** $DF(x_0,y_0)$ is the set-valued map from $X$ to $Y$ whose graph is the contingent cone to the graph of $F$:
--
--   $$
--   v_0\in DF(x_0,y_0)(u_0)\iff (u_0,v_0)\in T_{\operatorname{graph}(F)}(x_0,y_0).
--   $$
--
--   It is used at all points of the graph near the base point, in the hypothesis of the quantitative Theorem 2 of §3.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, (1), p.13

import Mathlib
import Definitions.Def_AubinLipschitz_contingentCone
import Definitions.Def_AubinLipschitz_graphOf

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, (1), p.13: the *contingent derivative* `DF(x₀, y₀) : X ⇉ Y`, whose graph is the
contingent cone `T_graph(F)(x₀, y₀)`: `v₀ ∈ DF(x₀, y₀)(u₀)` iff
`(u₀, v₀) ∈ T_graph(F)(x₀, y₀)`.

**Formalization Note** The cone is taken in `X × Y` with Lean's sup norm. The contingent cone is
unchanged by passing to an equivalent norm, so nothing depends on this. -/
def contingentDeriv {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Set Y) (x₀ : X) (y₀ : Y) : X → Set Y :=
  fun u₀ => {v₀ | (u₀, v₀) ∈ contingentCone (graphOf F) (x₀, y₀)}

end AubinLipschitz


