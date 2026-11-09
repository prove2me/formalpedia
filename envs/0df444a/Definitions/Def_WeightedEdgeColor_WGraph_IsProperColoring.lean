-- Prove2me | Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
-- name    : WeightedEdgeColor_WGraph_IsProperColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:42.941303+00:00
-- url     : https://prove2.me/theorems/74c8e82a-deeb-4d9e-ba29-964e2188fee4
-- title:
--   Proper weighted coloring: at every vertex each color class has incident weight at most one
-- statement:
--   Let $G=(V,E)$ be an edge-weighted graph with weights $w:E\to(0,1]$. A coloring $\varphi:E\to\kappa$ of the edges with a palette $\kappa$ is a **proper weighted coloring** if, at every vertex $v$ and for every color $c$,
--   $$
--   \sum_{e\ni v,\ \varphi(e)=c} w_e\le 1 .
--   $$
--   The weighted chromatic index $\chi'_w(G)$ is the least number of colors in a proper weighted coloring.
--
--   When all weights are one this is ordinary proper edge coloring; for a star it is bin packing.
--
--   **Formalization Note** The palette is an arbitrary type and not every color has to be used. Statements of the form $\chi'_w(G)\le X$ are written as "there is $k\le X$ and a proper weighted coloring $E\to\{0,\dots,k-1\}$", so no infimum is taken.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), §1, p.1

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace WGraph

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- A proper weighted coloring: at every vertex `v` and for each color `c`, the incident edges
of color `c` have total weight at most one.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
§1, p.1.

**Formalization Note.** The palette is any type `κ`; colors need not all be used. The paper's
`χ′_w(G) ≤ X` is stated in theorems as "there are `k ≤ X` and a proper weighted coloring
`E → Fin k`", so no infimum (and no junk value) is involved. -/
def IsProperColoring (G : WGraph V E) {κ : Type} [DecidableEq κ] (φ : E → κ) : Prop :=
  ∀ (v : V) (c : κ), ∑ e ∈ (G.inc v).filter (fun e => φ e = c), G.w e ≤ 1

end WGraph

end WeightedEdgeColor


