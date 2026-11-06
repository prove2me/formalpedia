-- Prove2me | Definitions.Def_IPMJumpLB_shortcutDemGap
-- name    : IPMJumpLB_shortcutDemGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:55.459882+00:00
-- url     : https://prove2.me/theorems/1c92444b-0313-444d-ad46-62df2514cc59
-- title:
--   Shortcut-demand gap term $D_{S,\mathrm{dem}}$
-- statement:
--   For a potential $x$ (slacks $s = c - Bx$) and a flow $f$ on the Section 4 instance,
--   $$
--   D_{S,\mathrm{dem}} = \sum_{j=1}^{(b-2)k^2} s_{(v_0, a_j)} \bigl(f_{(v_0, a_j)} - f_{(a_j, v_k)}\bigr),
--   $$
--   the part of the duality gap due to the unit of flow absorbed at each shortcut vertex $a_j$. Under flow conservation it equals $\sum_j s_{(v_0, a_j)}$.
--
--   **Formalization Note** The definition is the page's defining expression; the simplification to $\sum_j s_{(v_0, a_j)}$, which uses conservation at $a_j$, is not built in.
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

/-- `D_S,dem = ∑_j s_(v₀, a_j) (f_(v₀, a_j) − f_(a_j, v_k))`, the part of the duality gap of the
Section 4 instance due to the unit absorbed at each shortcut vertex `a_j`
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.11).

**Formalization Note** This is the defining expression of the page; the page's simplification to
`∑_j s_(v₀, a_j)` uses flow conservation at `a_j` and is not built in. -/
noncomputable def shortcutDemGap (b k : ℕ) (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) : ℝ :=
  ∑ j : Fin ((b - 2) * k ^ 2), slack (unitSSSP b k) x (.scIn j) * (f (.scIn j) - f (.scOut j))

end IPMJumpLB


