-- Prove2me | Definitions.Def_FASTournament_MobiusFree
-- name    : FASTournament_MobiusFree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:24.423121+00:00
-- url     : https://prove2.me/theorems/831192d9-b929-4a74-b123-beac8a3d79f4
-- title:
--   Möbius-free tournament
-- statement:
--   A tournament is **Möbius-free** if it contains none of the four Möbius ladders $K_{3,3}$, $K'_{3,3}$, $M_5$ and $M_5^*$ of Figure 1 as a subgraph (not necessarily induced).
--
--   These four ladders are the only obstructions to cycle ideal and cycle Mengerian tournaments (Theorem 1.1), and Theorem 1.2 shows they are also the only obstructions to FAS ideal and FAS Mengerian tournaments.
--
--   **Formalization Note** The predicate is defined for every digraph; the paper applies it to tournaments.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3, Figure 1

import Mathlib
import Definitions.Def_FASTournament_ContainsSubgraph
import Definitions.Def_FASTournament_K33
import Definitions.Def_FASTournament_K33prime
import Definitions.Def_FASTournament_M5
import Definitions.Def_FASTournament_M5star

namespace FASTournament

/-- **Möbius-free tournament.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3: "We call a tournament Möbius-free if it contains none of K3,3, K′3,3, M5, and M∗5
depicted in Figure 1 as a subgraph".

**Formalization Note.** Containment is not necessarily induced (`ContainsSubgraph`). The
predicate is stated for every digraph; the paper applies it to tournaments. -/
def MobiusFree {V : Type*} (G : Digraph V) : Prop :=
  ¬ ContainsSubgraph K33 G ∧ ¬ ContainsSubgraph K33prime G ∧ ¬ ContainsSubgraph M5 G ∧
    ¬ ContainsSubgraph M5star G

end FASTournament


