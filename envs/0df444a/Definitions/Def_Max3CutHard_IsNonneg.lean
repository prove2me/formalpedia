-- Prove2me | Definitions.Def_Max3CutHard_IsNonneg
-- name    : Max3CutHard_IsNonneg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:03.012201+00:00
-- url     : https://prove2.me/theorems/3629c2e9-1bd0-45f3-80a3-842dfa1267af
-- title:
--   Non-negative edge weights
-- statement:
--   A weighted graph has **non-negative edge weights** if $w_{ab}\ge0$ for every edge. This is the standing assumption on graphs in Section 2.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_Max3CutHard_RGraph

namespace Max3CutHard

/-- **Non-negative edge weights.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4: "A (weighted) graph
`G = (V, E, w)` has non-negative edge weights". -/
def IsNonneg {V : Type} (G : RGraph V) : Prop := ∀ e ∈ G, 0 ≤ e.2

end Max3CutHard


