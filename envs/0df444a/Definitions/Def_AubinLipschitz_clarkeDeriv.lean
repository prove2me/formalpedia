-- Prove2me | Definitions.Def_AubinLipschitz_clarkeDeriv
-- name    : AubinLipschitz_clarkeDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:05.250563+00:00
-- url     : https://prove2.me/theorems/2d9bc7cc-78da-48bc-a7ae-de99aaa7ffc2
-- title:
--   §2, (13) and Definition 2 — the Clarke derivative $CF(x_0,y_0)$
-- statement:
--   Let $F$ be a set-valued map between normed spaces $X$ and $Y$, and $(x_0,y_0)$ a point of its graph. The **Clarke derivative** $CF(x_0,y_0)$ is the set-valued map from $X$ to $Y$ whose graph is the Clarke tangent cone to the graph of $F$:
--
--   $$
--   v_0\in CF(x_0,y_0)(u_0)\iff (u_0,v_0)\in C_{\operatorname{graph}(F)}(x_0,y_0).
--   $$
--
--   It is the derivative in the hypotheses of the Inverse Function Theorem and in the formula of the goal.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, (13) and Definition 2, p.16

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeCone
import Definitions.Def_AubinLipschitz_graphOf

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, (13) and Definition 2, p.16: the *Clarke derivative* `CF(x₀, y₀) : X ⇉ Y`, whose
graph is the Clarke tangent cone `C_graph(F)(x₀, y₀)`: `v₀ ∈ CF(x₀, y₀)(u₀)` iff
`(u₀, v₀) ∈ C_graph(F)(x₀, y₀)`.

**Formalization Note** The cone is taken in `X × Y` with Lean's sup norm. The Clarke cone is
unchanged by passing to an equivalent norm, so nothing depends on this. -/
def clarkeDeriv {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Set Y) (x₀ : X) (y₀ : Y) : X → Set Y :=
  fun u₀ => {v₀ | (u₀, v₀) ∈ clarkeCone (graphOf F) (x₀, y₀)}

end AubinLipschitz


