-- Prove2me | Definitions.Def_RoslingAssembly_Network_P
-- name    : RoslingAssembly_Network_P
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:28.159141+00:00
-- url     : https://prove2.me/theorems/47f9fb27-73e8-42de-9474-f321e35c7eeb
-- title:
--   Immediate predecessors $P(i)$ of an item
-- statement:
--   For an item $i$ of an assembly network, $P(i)=\{k : s(k)=i\}$ is the set of **immediate predecessors** of $i$: the components assembled directly into $i$. Items with $P(i)=\emptyset$ are purchased from outside.
--
--   $P(i)$ defines the echelon holding costs $h_i=H_i-\sum_{k\in P(i)}H_k$ and the assembly constraints $Y_{it}\le X^l_{kt}$, $k\in P(i)$, of problem P.
--
--   **Formalization Note** Items are `Fin N`, 0-based. The paper also lists $P(0)$ for its sentinel item $0$; it is not needed.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib
import Definitions.Def_RoslingAssembly_Network

namespace RoslingAssembly

/-- **Immediate predecessors** P(i) (§1, p. 566). Rosling, *Optimal Inventory Policies for
Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"P(i) = the set of immediate predecessors of item i = 0, 1, . . . , N;".

`net.P i` is the set of items `k` whose immediate successor is `i` (`s k = some i`): the
components assembled directly into `i`.

**Formalization Note.** Items are `Fin N`, 0-based (paper item `i` is Lean item `i − 1`). The
paper also lists P(0) for its sentinel item 0 (the end item); that set is not used here. -/
def Network.P {N : ℕ} (net : Network N) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun k => net.s k = some i)

end RoslingAssembly


