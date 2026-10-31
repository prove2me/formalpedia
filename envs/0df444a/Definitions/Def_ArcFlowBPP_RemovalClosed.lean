-- Prove2me | Definitions.Def_ArcFlowBPP_RemovalClosed
-- name    : ArcFlowBPP_RemovalClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:06.902278+00:00
-- url     : https://prove2.me/theorems/d67346bf-bd5a-4a59-9225-a0da627a042e
-- title:
--   Pattern set closed under removing one item
-- statement:
--   A set $P \subseteq \mathbb N^m$ of patterns is **closed under removing one item** if for every pattern $p \in P$ and every item $i$ with $p_i \ge 1$, the pattern $p - e_i$ (one copy of item $i$ removed) either belongs to $P$ or is the zero pattern.
--
--   This is the property of "all valid packing patterns" that the proof of Property 1 uses: when the demand of an item is met with excess, a pattern can be replaced by one "that do[es] not include the items whose demands are being satisfied with excess (recall that every valid packing pattern is represented in the graph)". The sets of valid patterns of the paper (knapsack patterns (9), vector-packing patterns (25), either one intersected with $x \le b$), without the empty pattern, are closed under removing one item.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, proof of Property 1, p.7; §2.2, eq. (9), p.4

import Mathlib

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, Property 1 and its proof, p.7: the hypothesis "a graph with all valid packing
patterns represented as paths from s to t", as the proof uses it: when an item is satisfied with
excess, a pattern containing it can be replaced by the pattern without one copy of it ("recall
that every valid packing pattern is represented in the graph").
`RemovalClosed P`: removing one copy of an item from a pattern of `P` gives a pattern of `P` or
the zero pattern.

**Formalization Note.** The paper's sets of valid patterns (knapsack patterns (9) on p.4,
vector-packing patterns (25), either one intersected with `x ≤ b`), with the empty pattern
removed, are closed under removing one item, so the paper's hypothesis implies this one; it is
used as a weaker (more general) hypothesis on the set of path patterns. -/
def RemovalClosed {m : ℕ} (P : Set (Fin m → ℕ)) : Prop :=
  ∀ p ∈ P, ∀ i : Fin m, 1 ≤ p i → (p - Pi.single i 1 ∈ P ∨ p - Pi.single i 1 = 0)

end ArcFlowBPP


