-- Prove2me | Definitions.Def_PivotADO_OneHop_PathSystem
-- name    : PivotADO_OneHop_PathSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:53.742583+00:00
-- url     : https://prove2.me/theorems/aa27084b-cb47-4673-8b1f-bbc5d39e83c4
-- title:
--   Fixed reversal-consistent shortest-path system
-- statement:
--   For each reachable ordered pair $u,v$ in $G$, fix one shortest walk $P(u,v)$, with
--
--   $$|P(u,v)|=\delta_G(u,v),\qquad P(v,u)=\operatorname{reverse}(P(u,v)).$$
--
--   Shortestness makes each walk a path. No path is assigned to an unreachable pair. This is the source's fixed system, quantified over wherever alignment is used; choices for different pairs are not assumed consistent under restriction to subpaths. In particular, alignment is not existence of a convenient shortest path.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §2 shortest-path convention, p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false

namespace PivotADO.OneHop

/-- The single fixed reversal-consistent shortest-path system of §2, p.5.
Only reachable pairs have a path. Length equality to edist specifies shortestness. -/
structure PathSystem {V : Type*} (G : SimpleGraph V) where
  path : ∀ u v, G.Reachable u v → G.Walk u v
  shortest : ∀ u v (h : G.Reachable u v),
    ((path u v h).length : ℕ∞) = G.edist u v
  reverse : ∀ u v (h : G.Reachable u v),
    path v u h.symm = (path u v h).reverse

end PivotADO.OneHop


