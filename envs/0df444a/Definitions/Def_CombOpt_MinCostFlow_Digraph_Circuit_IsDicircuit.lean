-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_IsDicircuit
-- name    : CombOpt_MinCostFlow_Digraph_Circuit_IsDicircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:52.193879+00:00
-- url     : https://prove2.me/theorems/dafa19ef-96b9-477e-aae9-769178173a9a
-- title:
--   Dicircuit
-- statement:
--   A **dicircuit** is a circuit all of whose arcs are forward, i.e. a closed directed path with distinct arcs, distinct inner nodes and at least one arc. A loop is a dicircuit of length one.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, pp. 19–20 (PDF pp. 28–29)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit

namespace CombOpt.MinCostFlow

/-- **A dicircuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, pp. 19–20 (PDF pp. 28–29): "A path in which every arc is forward is a directed path
or *dipath*. A *dicircuit* is a dipath that is also a circuit."

`C.IsDicircuit` holds when every arc of the circuit `C` is traversed forward. -/
def Digraph.Circuit.IsDicircuit {V E : Type*} {G : Digraph V E} (C : G.Circuit) : Prop :=
  ∀ i, C.forward i = true

end CombOpt.MinCostFlow


