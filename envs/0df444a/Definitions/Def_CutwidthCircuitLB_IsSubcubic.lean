-- Prove2me | Definitions.Def_CutwidthCircuitLB_IsSubcubic
-- name    : CutwidthCircuitLB_IsSubcubic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:51.943279+00:00
-- url     : https://prove2.me/theorems/ad49cb80-db1e-4e0a-934a-d0dc21fae0d9
-- title:
--   Subcubic multigraph (maximum degree at most $3$)
-- statement:
--   A multigraph is **subcubic** if every vertex has degree at most $3$, edges being counted with multiplicity.
--
--   **Formalization Note** The multigraph is the published `CombOpt.MatchingPolytope.Graph` (a vertex type, an edge type, and for each edge the unordered pair of its ends). The degree of $v$ is the number of edges having $v$ as an end; for a loopless multigraph, the case of every use in the mission, this is the usual degree.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.1, p.2, and Definition 2.5, p.8

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CutwidthCircuitLB

/-- A multigraph is **subcubic** (maximum degree at most `3`) (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.1, p.2, and Definition 2.5,
p.8): every vertex is an end of at most three edges, counted with multiplicity.

**Formalization Note** The multigraph is the published `CombOpt.MatchingPolytope.Graph V E`
(edges `E`, each with an unordered pair of ends `ends e : Sym2 V`; parallel edges and loops
allowed). The degree of `v` is the number of edges `e` with `v ∈ ends e`; for a
loopless multigraph (every use in the paper) this is the usual degree. -/
def IsSubcubic {V E : Type*} [Fintype E] [DecidableEq V] (G : CombOpt.MatchingPolytope.Graph V E) : Prop :=
  ∀ v : V, (Finset.univ.filter (fun e => v ∈ G.ends e)).card ≤ 3

end CutwidthCircuitLB


