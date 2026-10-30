-- Prove2me | Definitions.Def_Timetabling_StableHalf_IsClosed
-- name    : Timetabling_StableHalf_IsClosed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:21.633788+00:00
-- url     : https://prove2.me/theorems/723ea6aa-74f8-4370-a093-0850f6773d69
-- title:
--   Partial assignment closed under implications
-- statement:
--   Let $G$ be a graph on the nodes $x_j, \bar x_j$ ($j = 1, \dots, n$). A **partial assignment** $a$ fixes, for some pairs $j$, one node $(j, b)$ as *chosen* (its mate $(j, \lnot b)$ is then excluded) and leaves the other pairs open. It is **closed** in $G$ when every node adjacent to a chosen node lies in an assigned pair whose other node is chosen:
--
--   $$
--   a_{u_1} = u_2 \ \text{ and } \ u \sim_G w \quad \Longrightarrow \quad a_{w_1} = \lnot w_2 .
--   $$
--
--   Closedness says that all implications of the chosen nodes have been taken into account: no chosen node is adjacent to an open pair. It implies that the chosen nodes are pairwise non-adjacent. The assignment with every pair open is closed. It is the invariant maintained by the limited backtracking of Proposition 2.4 between two decisions.
--
--   **Formalization Note** A partial assignment is `a : Fin n → Option Bool`; `a j = some b` means node `(j, b)` is chosen and `a j = none` means pair `j` is open.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "then one considers all the implications of this choice". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.StableHalf

/-- **A partial assignment closed under implications.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155,
"then one considers all the implications of this choice. This may fix the schedules of some
other teachers."

A partial assignment `a : Fin n → Option Bool` fixes the node `(j, b)` of pair `j` when
`a j = some b` (the node is *chosen*, its mate `(j, !b)` is excluded) and leaves pair `j` open
when `a j = none`. It is *closed* in `G` when every node adjacent to a chosen node lies in an
assigned pair whose other node is chosen: if `a u.1 = some u.2` and `G.Adj u w`, then
`a w.1 = some (!w.2)`.

**Formalization Note.** Closedness says that all implications of the chosen nodes have been
taken into account. It implies that the chosen nodes are pairwise non-adjacent (if `u`, `w` were
both chosen and adjacent, pair `w.1` would be assigned both `w.2` and `!w.2`). The assignment
with every pair open is closed. -/
def IsClosed {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (a : Fin n → Option Bool) : Prop :=
  ∀ u : Fin n × Bool, a u.1 = some u.2 → ∀ w : Fin n × Bool, G.Adj u w → a w.1 = some (!w.2)

end Timetabling.StableHalf


