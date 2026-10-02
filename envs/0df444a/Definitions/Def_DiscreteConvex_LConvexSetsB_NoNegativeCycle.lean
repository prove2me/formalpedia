-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_NoNegativeCycle
-- name    : DiscreteConvex_LConvexSetsB_NoNegativeCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:44:01.32778+00:00
-- url     : https://prove2.me/theorems/b3b6264c-4ee3-46a4-997c-d9762803411a
-- title:
--   NoNegativeCycle
-- statement:
--   The graph $G_\gamma$ associated with $\gamma$ (Eq. (5.1)) has **no negative cycle**: every closed walk of positive length has nonnegative total $\gamma$-length.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_WalkLength

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122: the absence of a negative cycle
in the graph `Gγ` associated with a distance function, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The graph `Gγ` associated with `γ` (Eq. (5.1)) has **no negative cycle**: every closed
walk of positive length has nonnegative total `γ`-length. A closed walk using an edge outside
`Gγ` (`γ = ⊤`) automatically has length `⊤ ≥ 0`, so restricting to `Gγ`'s own edges is
automatic. -/
def NoNegativeCycle {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ w : Fin (k + 1) → V, w 0 = w (Fin.last k) → 0 ≤ WalkLength γ k w

end DiscreteConvex.LConvexSetsB


