-- Prove2me | Definitions.Def_RoslingAssembly_Network_M
-- name    : RoslingAssembly_Network_M
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:41.247278+00:00
-- url     : https://prove2.me/theorems/902e5eeb-c065-4616-a24b-b7d56e68a137
-- title:
--   Total lead time $M_i$ of an item and its successors
-- statement:
--   Let $l_i\in\{0,1,2,\dots\}$ be the lead time of item $i$: an order for assembly (or purchase) of $i$ placed in period $t$ arrives in period $t+l_i$. The **total lead time** of item $i$ is the lead time of $i$ and all its successors,
--   $$M_i=l_i+\sum_{k\in A(i)}l_k .$$
--   In particular $M_1=l_1$ for the end item.
--
--   $M_i$ measures how many periods before a customer demand an order for item $i$ must be placed; the discount factors $\alpha^{-M_{s(i)}}$ of the Generalized Assumption and of Theorem 4 are built from it.
--
--   **Formalization Note** Defined as printed, as a sum over all successors; the recursion $M_i=l_i+M_{s(i)}$ is a separate milestone. Items are `Fin N`, 0-based.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §2, p. 567

import Mathlib
import Definitions.Def_RoslingAssembly_Network_A

namespace RoslingAssembly

/-- **Total lead time** M_i (§2, p. 567). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, §2, p. 567 (unnumbered):
"M_i = total lead-time for item i and all its successors; M_0 = 0 and M_i = l_i + Σ_{k∈A(i)} l_k
for i = 1, 2, . . . N."; p. 566: "l_i = number of periods (lead-time) for assembly (or delivery)
of item i."

Given lead times `ℓ : Fin N → ℕ`, `net.M ℓ i = ℓ i + Σ_{k ∈ A(i)} ℓ k`.

**Formalization Note.** Defined as printed (a sum over all successors), not by the recursion
`M_i = l_i + M_{s(i)}`, which is a separate statement. Items are `Fin N`, 0-based (paper item `i`
is Lean item `i − 1`); lead times are natural numbers, zero allowed. The sentinel `M_0 = 0` is
built into `Network.Ms`. -/
noncomputable def Network.M {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) : ℕ :=
  ℓ i + ∑ k ∈ net.A i, ℓ k

end RoslingAssembly


