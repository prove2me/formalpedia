-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsAugmenting
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsAugmenting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:25.937365+00:00
-- url     : https://prove2.me/theorems/79b98771-9768-4f23-a19b-e4b12c4b1ef4
-- title:
--   $M$-augmenting path
-- statement:
--   A path $P$ from $u$ to $w$ is **$M$-augmenting** if it is simple and $M$-alternating, $u\ne w$, and both $u$ and $w$ are $M$-exposed.
--
--   **Formalization Note** The book's definition asks for an $M$-alternating path with distinct, $M$-exposed end nodes, and its word "path" allows repeated nodes. Simplicity is added because Theorem 5.1 fails without it: see the differences listed on that theorem.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 128 (PDF p. 136)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsSimple
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsAlternating

namespace CombOpt.TutteBerge

/-- **An `M`-augmenting path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 128 (PDF p. 136): "If, in addition, the end nodes of P are distinct and are both
M-exposed, then P is an *M-augmenting* path."

**Formalization Note.** `P` is required to be simple. The book's word "path" (p. 10) allows repeated
nodes, but the book uses augmenting paths through the symmetric difference M △ E(P) (p. 129), and
without simplicity Theorem 5.1 is false: see the differences recorded on `theorem_5_1`. Dropping
`u ≠ w` would make every one-node path at an exposed node augmenting. -/
def Multigraph.Path.IsAugmenting {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w)
    (M : Set E) : Prop :=
  P.IsSimple ∧ P.IsAlternating M ∧ u ≠ w ∧ u ∈ G.exposedNodes M ∧ w ∈ G.exposedNodes M

end CombOpt.TutteBerge


