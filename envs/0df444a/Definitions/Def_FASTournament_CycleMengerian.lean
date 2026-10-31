-- Prove2me | Definitions.Def_FASTournament_CycleMengerian
-- name    : FASTournament_CycleMengerian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:22.739082+00:00
-- url     : https://prove2.me/theorems/67449e23-320e-41ed-b905-0be486928e2e
-- title:
--   Cycle Mengerian (CM) digraph
-- statement:
--   Let $M$ be the **cycle-arc incidence matrix** of a digraph $G$: one row per directed cycle $C$, one column per arc, entry $1$ if $e\in C$. $G$ is **cycle Mengerian (CM)** if the system $\pi(G)$: $Mx\ge\mathbf 1,\ x\ge\mathbf 0$ is totally dual integral.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsDirCycle
import Definitions.Def_FASTournament_IsTDI

open Classical

namespace FASTournament

/-- **Cycle Mengerian (CM) digraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2: "Let M be the cycle-arc incidence matrix of G, let π(G) denote the linear system
Mx ≥ 1, x ≥ 0 … We say … that G is cycle Mengerian (CM) if π(G) is a TDI system."

`M` has one row per directed cycle `C` of `G` and one column per arc, with entry `1` if `e ∈ C`.

**Formalization Note.** Cycles are arc sets (`IsDirCycle`). Finite types are made `Fintype`
classically. -/
def CycleMengerian {V : Type*} [Finite V] (G : Digraph V) : Prop :=
  letI : Fintype V := Fintype.ofFinite V
  IsTDI (fun (C : {C : Finset (Arc G) // IsDirCycle G C}) (e : Arc G) =>
    if e ∈ C.1 then (1 : ℤ) else 0) (fun _ => 1)

end FASTournament


