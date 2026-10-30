-- Prove2me | Definitions.Def_RoslingAssembly_Network_A
-- name    : RoslingAssembly_Network_A
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:03.135136+00:00
-- url     : https://prove2.me/theorems/4f6e0079-356c-4af2-b0f2-4f8876320912
-- title:
--   All successors $A(i)$ of an item
-- statement:
--   For an item $i$ of an assembly network, $A(i)$ is the set of **all successors** of $i$: the items $s(i)$, $s(s(i))$, … reached by repeatedly passing to the immediate successor, up to and including the end item. The end item has $A(1)=\emptyset$.
--
--   $A(i)$ enters the total lead time $M_i$ of $i$ and, through $B(k)=\{k: i\in A(k)\}$, the set of predecessors.
--
--   **Formalization Note** $A(i)$ is the transitive closure of the successor relation, as a finite set of `Fin N`.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib
import Definitions.Def_RoslingAssembly_Network

namespace RoslingAssembly

/-- **All successors** A(i) (§1, p. 566). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"A(i) = the set of all successors of item i;".

`net.A i` is the set of items reached from `i` by one or more steps of the successor map `s`
(its transitive closure): `s(i)`, `s(s(i))`, … up to the end item.

**Formalization Note.** Items are `Fin N`, 0-based (paper item `i` is Lean item `i − 1`). The
end item has `A = ∅`. Membership is `Relation.TransGen` of the relation `s a = some b`, filtered
with classical decidability. -/
noncomputable def Network.A {N : ℕ} (net : Network N) (i : Fin N) : Finset (Fin N) :=
  @Finset.filter _ (fun k => Relation.TransGen (fun a b => net.s a = some b) i k)
    (Classical.decPred _) Finset.univ

end RoslingAssembly


