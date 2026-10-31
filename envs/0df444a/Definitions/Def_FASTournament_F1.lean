-- Prove2me | Definitions.Def_FASTournament_F1
-- name    : FASTournament_F1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:25.847563+00:00
-- url     : https://prove2.me/theorems/a33b32b4-1ebf-4ed5-a2cf-4df0dbcb8dc4
-- title:
--   The tournament $F_1=G_1-v_6$
-- statement:
--   $F_1$ is the subtournament of $G_1$ induced by the vertices $1,\dots,5$, i.e. $F_1$ arises from $G_1$ by deleting vertex $v_6$. Its arcs are $12,23,34,45,51,13,35,52,24,41$: it is the regular tournament on five vertices (every vertex has out-degree $2$), drawn in Figure 4. Together with $G_1$ it is one of the two exceptional Möbius-free strong tournaments that are not in $\mathcal P$.
--
--   **Formalization Note** `Fin.castSucc : Fin 5 → Fin 6` embeds the vertices $1,\dots,5$.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Figure 4; proof of Theorem 1.2, p.26

import Mathlib
import Definitions.Def_FASTournament_G1

namespace FASTournament

/-- **The tournament `F₁` = `G₁ − v₆`** (Figure 4).
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26: "F1 arises from G1 by deleting vertex v6 (see the labeling
in Figure 5)".

The subtournament of `G₁` induced by the vertices `1, …, 5`: the regular tournament on five
vertices (each vertex has out-degree `2`), as drawn in Figure 4.

**Formalization Note.** `Fin.castSucc : Fin 5 → Fin 6` is the inclusion of vertices `1, …, 5`
(indices `0, …, 4`). -/
def F1 : Digraph (Fin 5) where
  Adj a b := G1.Adj a.castSucc b.castSucc

end FASTournament


