-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsCircuit
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:31.818084+00:00
-- url     : https://prove2.me/theorems/db3e4970-5bed-4da2-8ce5-77d4201f6261
-- title:
--   Circuit
-- statement:
--   A closed path $v_0,e_1,\dots,e_k,v_k=v_0$ is a **circuit** if $e_1,\dots,e_k$ are distinct, $v_0,\dots,v_{k-1}$ are distinct, and $k\ge 1$.
--
--   A loop is a circuit of length $1$, and two parallel edges form a circuit of length $2$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edges
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_length

namespace CombOpt.TutteBerge

/-- **A circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "it is a *circuit* if it is edge-simple and closed, v₀, …, v_{k−1}
are distinct, and k ≥ 1."

The path is closed by its type (from `x` to `x`). The clauses are, in order: edge-simple
("e₁, …, e_k are distinct"), `v₀, …, v_{k−1}` distinct (the node list with its last entry `v_k`
dropped), and `k ≥ 1`.

**Formalization Note.** A loop gives a circuit of length 1, and two parallel edges give a circuit
of length 2, as in the book. -/
def Multigraph.Path.IsCircuit {V E : Type*} {G : Multigraph V E} {x : V} (C : G.Path x x) : Prop :=
  C.edges.Nodup ∧ C.nodes.dropLast.Nodup ∧ 1 ≤ C.length

end CombOpt.TutteBerge


