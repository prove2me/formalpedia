-- Prove2me | Definitions.Def_RoslingAssembly_Network_Ms
-- name    : RoslingAssembly_Network_Ms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:34:12.832053+00:00
-- url     : https://prove2.me/theorems/a8984e7d-d72d-4f5d-a1c0-29cabe0ab126
-- title:
--   Total lead time $M_{s(i)}$ of the immediate successor
-- statement:
--   For an item $i$, $M_{s(i)}$ is the total lead time of its immediate successor $s(i)$, with the convention $M_{s(1)}=M_0=0$ for the end item.
--
--   These numbers are the exponents in the condition $h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}}<0$ of Theorem 4(i).
--
--   **Formalization Note** Items are `Fin N`, 0-based; the paper's sentinel item $0$ is `none`, mapped to $0$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566; §2, p. 567

import Mathlib
import Definitions.Def_RoslingAssembly_Network_M

namespace RoslingAssembly

/-- **Total lead time of the successor** M_{s(i)} (§2, p. 567). Rosling, *Optimal Inventory
Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 566:
"for notational convenience we define s(1) = 0"; p. 567: "M_0 = 0".

`net.Ms ℓ i` is the paper's `M_{s(i)}`: the total lead time `M_j` of the immediate successor `j`
of `i`, and `0` for the end item (the paper's `M_{s(1)} = M_0 = 0`).

**Formalization Note.** Items are `Fin N`, 0-based; the paper's sentinel item 0 is `none`. -/
noncomputable def Network.Ms {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) : ℕ :=
  match net.s i with
  | none => 0
  | some j => net.M ℓ j

end RoslingAssembly


