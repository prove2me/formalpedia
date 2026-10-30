-- Prove2me | Definitions.Def_RoslingAssembly_Network_B
-- name    : RoslingAssembly_Network_B
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:05.668773+00:00
-- url     : https://prove2.me/theorems/25f9080c-e100-41d5-8291-643efcb066f2
-- title:
--   All predecessors $B(i)$ of an item
-- statement:
--   For an item $i$ of an assembly network, $B(i)=\{k : i\in A(k)\}$ is the set of **all predecessors** of $i$: every item that is, directly or through intermediate subassemblies, assembled into $i$.
--
--   The subsystem $\{i\}\cup B(i)$ is the one perturbed in the proof of Theorem 4(i), and $B(i)$ is the index set of the sums in the Generalized Assumption.
--
--   **Formalization Note** Items are `Fin N`, 0-based.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib
import Definitions.Def_RoslingAssembly_Network_A

namespace RoslingAssembly

/-- **All predecessors** B(i) (§1, p. 566). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"B(i) = the set of all predecessors of item i;".

`net.B i` is the set of items `k` of which `i` is a direct or indirect successor, `i ∈ A(k)`.

**Formalization Note.** Items are `Fin N`, 0-based (paper item `i` is Lean item `i − 1`). -/
noncomputable def Network.B {N : ℕ} (net : Network N) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun k => i ∈ net.A k)

end RoslingAssembly


