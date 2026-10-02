-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_ShortestDist
-- name    : DiscreteConvex_LConvexSetsB_ShortestDist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:06.938547+00:00
-- url     : https://prove2.me/theorems/0afb493c-44b0-4167-b32d-37d811006a22
-- title:
--   ShortestDist
-- statement:
--   The **shortest-path closure** $\bar\gamma(u,v)$: the infimum length of a walk from $u$ to $v$ in $G_\gamma$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_WalkLength

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122: the shortest-path closure `γ̄` of a
distance function, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

open Classical in
/-- The **shortest-path closure** `γ̄(u,v)`: the infimum length of a walk from `u` to `v` in
`Gγ` (the empty walk, `k=0`, covers `u=v` with length `0`; the infimum is `⊤` if no walk
exists). -/
noncomputable def ShortestDist {V : Type*} [Fintype V] (γ : V → V → WithTop ℝ) (u v : V) :
    WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ k : ℕ, ∃ w : Fin (k + 1) → V,
    w 0 = u ∧ w (Fin.last k) = v ∧ L = WalkLength γ k w}

end DiscreteConvex.LConvexSetsB


