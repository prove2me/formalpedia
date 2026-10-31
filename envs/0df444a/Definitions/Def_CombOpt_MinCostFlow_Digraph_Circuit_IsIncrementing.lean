-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_IsIncrementing
-- name    : CombOpt_MinCostFlow_Digraph_Circuit_IsIncrementing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:01.873505+00:00
-- url     : https://prove2.me/theorems/bd8a818f-bc18-476d-923b-cabfd538fb84
-- title:
--   $x$-incrementing circuit
-- statement:
--   For a flow $x$ and capacities $u$, a circuit (or path) is **$x$-incrementing** if every forward arc $e$ has $x_e<u_e$ and every reverse arc $e$ has $x_e>0$. Flow can then be raised on the forward arcs and lowered on the reverse arcs while staying within the bounds.
--
--   **Formalization Note** The comparison $x_e<u_e$ is made in the extended reals, so it holds whenever $u_e=\infty$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 41 (PDF p. 50)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit

namespace CombOpt.MinCostFlow

/-- **An x-incrementing circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 41 (PDF p. 50): "We call a path x-incrementing if every forward arc e has
x_e < u_e and every reverse arc e has x_e > 0."

**Formalization Note.** `x_e < u_e` is compared in `EReal`, so it always holds when `u_e = ∞`. -/
def Digraph.Circuit.IsIncrementing {V E : Type*} {G : Digraph V E} (C : G.Circuit)
    (u : E → EReal) (x : E → ℝ) : Prop :=
  ∀ i, (C.forward i = true → (x (C.arc i) : EReal) < u (C.arc i)) ∧
    (C.forward i = false → 0 < x (C.arc i))

end CombOpt.MinCostFlow


