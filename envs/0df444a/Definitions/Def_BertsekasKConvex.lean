-- Prove2me | Definitions.Def_BertsekasKConvex
-- name    : BertsekasKConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-08T00:36:45.104405+00:00
-- url     : https://prove2.me/theorems/39da5178-ce69-4877-98cc-aad47fc3c50b
-- title:
--   $K$-convexity (Def. 4.2.1)
-- statement:
--   **Definition 4.2.1 ($K$-convexity).** For a scalar $K$, a real-valued function $g$ on the line is **$K$-convex** if
--
--   $$K + g(z + y) \;\ge\; g(y) \;+\; \frac{z}{b}\,\bigl(g(y) - g(y - b)\bigr) \qquad \text{for all } z \ge 0, \; b > 0, \; y \in \mathbb{R}.$$
--
--   Reading the right-hand side geometrically: the chord slope of $g$ over $[y-b, y]$, extrapolated forward by the amount $z$, must not exceed $g(z+y)$ by more than $K$. For $K = 0$ this is a form of convexity; for $K > 0$ it relaxes convexity by exactly the fixed ordering cost.
--
--   The notion exists to handle inventory problems with a **fixed ordering cost** $K$: there the one-stage cost functions are not convex, but they are $K$-convex, and $K$-convexity is exactly the property preserved by the dynamic programming recursion. It is the analytical engine behind the optimality of $(s,S)$ policies — order up to $S$ when stock falls below $s$, do nothing otherwise — which is one of the foundational structural results of inventory theory.
--
--   **Formalization Note** The definition places no sign restriction on $K$, but taking $z = 0$ gives $g(y) \le K + g(y)$, so $K \ge 0$ is forced whenever the property is satisfiable; the source states it for $K \ge 0$. Since $b > 0$ is required, the quotient $z/b$ is never a division by zero. No continuity, measurability or boundedness of $g$ is assumed.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Definition 4.2.1

import Mathlib

/-- Definition 4.2.1 of Bertsekas, "Dynamic Programming and Optimal Control",
Vol. I, 3rd ed.: a real-valued function `g` is `K`-convex (`K ≥ 0`) if
`K + g(z + y) ≥ g(y) + z * (g(y) - g(y - b)) / b` for all `z ≥ 0`, `b > 0`
and `y`.  This is the notion underlying the optimality of multiperiod `(s, S)`
inventory policies. -/
def BertsekasKConvex (K : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ z b y : ℝ, 0 ≤ z → 0 < b →
    g y + (z / b) * (g y - g (y - b)) ≤ K + g (z + y)


