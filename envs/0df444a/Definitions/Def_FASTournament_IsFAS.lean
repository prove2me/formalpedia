-- Prove2me | Definitions.Def_FASTournament_IsFAS
-- name    : FASTournament_IsFAS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:22.275382+00:00
-- url     : https://prove2.me/theorems/18b0e2f2-9958-490f-8c19-eaf71d72f5ef
-- title:
--   Feedback arc set (FAS)
-- statement:
--   A set $F$ of arcs of a digraph $G$ is a **feedback arc set (FAS)** if $G\setminus F$ contains no directed cycle, i.e. every directed cycle of $G$ contains an arc of $F$.
--
--   If $G$ has no directed cycle, every arc set, including $\emptyset$, is an FAS.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsDirCycle

namespace FASTournament

/-- **Feedback arc set (FAS).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2: "A subset F of arcs is called a feedback arc set (FAS) of G if G\F contains no
cycles (directed)."

`F` is an FAS of `G` if every directed cycle of `G` contains an arc of `F`, i.e. deleting `F`
leaves no directed cycle.

**Formalization Note.** A cycle of `G \ F` is exactly a cycle of `G` disjoint from `F`. -/
def IsFAS {V : Type*} (G : Digraph V) (F : Finset (Arc G)) : Prop :=
  ∀ C, IsDirCycle G C → ∃ e ∈ F, e ∈ C

end FASTournament


