-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_reducedCost
-- name    : CombOpt_HeldKarp_Graph_reducedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:41.178057+00:00
-- url     : https://prove2.me/theorems/77446631-0d8b-4bbc-b313-9ffacdd1505c
-- title:
--   Edge costs altered by node numbers
-- statement:
--   Given edge costs $c\in\mathbb R^E$ and **node numbers** $y\in\mathbb R^V$, the altered cost of an edge $e$ with ends $u,v$ is
--   $$\bar c_e=c_e-y_u-y_v .$$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, box "Held-Karp Bound", p. 255 (PDF p. 263)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph

namespace CombOpt.HeldKarp

/-- **The edge costs altered by node numbers, c̄_e = c_e − y_u − y_v.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, box
"Held-Karp Bound", p. 255 (PDF p. 263): "for each node v ∈ V let y_v be a real number. Now for each
edge e = uv ∈ E let c̄_e = c_e − y_u − y_v".

`G.reducedCost c y e = c e − (y u + y v)` where `u, v` are the ends of `e`.

**Formalization Note.** `y u + y v` is symmetric in the two ends, so it is computed on the unordered
pair `G.ends e` with `Sym2.lift`. For a loop at `u` it gives `c_e − 2 y_u`. -/
def Graph.reducedCost {V E : Type*} (G : Graph V E) (c : E → ℝ) (y : V → ℝ) (e : E) : ℝ :=
  c e - Sym2.lift ⟨fun u v => y u + y v, fun u v => add_comm (y u) (y v)⟩ (G.ends e)

end CombOpt.HeldKarp


