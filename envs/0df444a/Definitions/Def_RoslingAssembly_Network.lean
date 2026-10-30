-- Prove2me | Definitions.Def_RoslingAssembly_Network
-- name    : RoslingAssembly_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:30.715841+00:00
-- url     : https://prove2.me/theorems/4e89f650-2055-418f-b14e-e5326a57bf33
-- title:
--   Assembly network: a tree of $N$ items rooted in the end item
-- statement:
--   An **assembly system** has $N$ items (components, subassemblies, the end item), numbered $1,\dots,N$; item $1$ is the end item. Every item $i\ne 1$ has exactly one immediate successor $s(i)$, the item it is assembled into, and the end item has none (the paper writes $s(1)=0$). The items are indexed so that every successor of $i$ has a smaller index than $i$; in particular $s(i)<i$, so following successors from any item always ends at the end item, and the product network is a tree rooted in the end item.
--
--   The network is the structural datum of problem P: lead times, echelon costs and the assembly constraints (3) are all read off it.
--
--   **Formalization Note** Items are `Fin N`, 0-based: paper item $i$ is Lean item $i-1$ and the end item is Lean item $0$, whose successor is `none`. The paper's second indexing convention, $M_i\ge M_{i-1}$, is not imposed.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566; §2, p. 567

import Mathlib

namespace RoslingAssembly

/-- **Assembly network** (§1, p. 566). Rosling, *Optimal Inventory Policies for Assembly Systems
under Random Demands*, Operations Research 37(4), 1989, §1 "The Model", p. 566 (unnumbered):
"There are N items (components, subassemblies at different levels, the end item). They are
denoted i = 1, 2, . . . N. Item 1 is the end item. Each nonend item has exactly one successor item
so that the product network forms a tree rooted in the end item." and "s(i) = the unique
immediate successor of item i = 1, 2, . . . N; for notational convenience we define s(1) = 0";
p. 567: "The items are supposed to be indexed so that … k < i for all k ∈ A(i)."

A network on `N` items is the successor map `s`: `s i = some j` says that item `j` is the unique
immediate successor of item `i`, and `s i = none` says that `i` is the end item.

**Formalization Note.** Items are `Fin N`, 0-based: paper item `i` is Lean item `i − 1`, so the
end item (paper item 1) is Lean item `0`, and the paper's sentinel `s(1) = 0` is `s 0 = none`.
The field `s_lt` is the paper's indexing clause "k < i for all k ∈ A(i)" (equivalently
`s(i) < i`); it makes every chain of successors end at the end item, so the network is a tree
rooted in the end item. The paper's other indexing clause, `M_i ≥ M_{i−1}`, is not imposed. -/
structure Network (N : ℕ) where
  /-- The immediate successor of each item; `none` exactly for the end item `0`. -/
  s : Fin N → Option (Fin N)
  /-- Only the end item (Lean item `0`, paper item 1) has no successor. -/
  s_eq_none_iff : ∀ i, s i = none ↔ i.val = 0
  /-- Successors carry smaller indices (paper p. 567: "k < i for all k ∈ A(i)"). -/
  s_lt : ∀ i j, s i = some j → j < i

end RoslingAssembly


