-- Prove2me | Definitions.Def_IPMJumpLB_leafGap
-- name    : IPMJumpLB_leafGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:05.581651+00:00
-- url     : https://prove2.me/theorems/a313d183-c47e-40eb-a6c1-e432da5d838b
-- title:
--   Leaf-arc gap term $D_L$
-- statement:
--   For a potential $x$ (slacks $s = c - Bx$) and a flow $f$ on the Section 4 instance,
--   $$
--   D_L = \sum_{e \in E_{\mathrm{leaf}}} s_e f_e ,
--   $$
--   the contribution of the $2k^2 - k$ leaf arcs (the $k-1$ leaf arcs at each of $v_1, \dots, v_k$ and the further $k^2$ at $v_k$) to the duality gap.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP

namespace IPMJumpLB

/-- `D_L = ∑_(e ∈ E_leaf) s_e f_e`, the contribution of the leaf arcs to the duality gap of the
Section 4 instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.11): the `k − 1` leaf arcs at each
`v₁, …, v_k` and the further `k²` leaf arcs at `v_k`. -/
noncomputable def leafGap (b k : ℕ) (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) : ℝ :=
  (∑ i : Fin k, ∑ t : Fin (k - 1),
      slack (unitSSSP b k) x (.leafArc i t) * f (.leafArc i t)) +
    ∑ t : Fin (k ^ 2), slack (unitSSSP b k) x (.extraLeafArc t) * f (.extraLeafArc t)

end IPMJumpLB


