-- Prove2me | Definitions.Def_WeightedEdgeColor_Supplement_IsBipartite
-- name    : WeightedEdgeColor_Supplement_IsBipartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:36:48.513201+00:00
-- url     : https://prove2.me/theorems/4d170115-f61d-435c-981e-0896cd246939
-- title:
--   Bipartite weighted multigraph
-- statement:
--   A weighted multigraph $G=(V,E)$ is **bipartite** if its vertex set can be split into two sides so that every edge has one endpoint on each side; that is, there is a map $s:V\to\{0,1\}$ with $s(u)\ne s(v)$ for every edge $e$ with endpoints $u,v$.
--
--   Parallel edges are allowed. Bipartite multigraphs are the class of Kőnig's theorem and of the Chung–Ross conjecture; the paper's Theorems D.3, E.4, E.5 and E.10 are stated for them.
--
--   **Formalization Note** The paper uses the standard notion without a definition. Loops are already excluded by the graph model, and the graph with no edges is bipartite.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorems D.3, E.4, E.5, E.10, pp.60, 64, 65, 70 (used without definition)

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- `G` is a bipartite weighted multigraph: its vertices can be split into two sides so that
every edge joins the two sides.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped), used without definition in
Theorems D.3, E.4, E.5, E.10, pp.60, 64, 65, 70.

**Formalization Note.** The standard notion: a side map `side : V → Bool` such that the two
endpoints of every edge lie on different sides. Parallel edges are allowed (the carrier is a
multigraph), loops are already excluded by `WGraph`, and the graph with no edges is bipartite. -/
def IsBipartite {V E : Type} (G : WGraph V E) : Prop :=
  ∃ side : V → Bool, ∀ (e : E) (u v : V), G.ends e = s(u, v) → side u ≠ side v

end Supplement

end WeightedEdgeColor


