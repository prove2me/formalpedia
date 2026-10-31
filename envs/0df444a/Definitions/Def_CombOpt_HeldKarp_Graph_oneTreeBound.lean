-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeBound
-- name    : CombOpt_HeldKarp_Graph_oneTreeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:45.178202+00:00
-- url     : https://prove2.me/theorems/a65c49f3-4484-4990-ab2e-69047b246cf5
-- title:
--   The 1-tree bound $A+B$
-- statement:
--   For edge costs $c\in\mathbb R^E$ and a node $v_1$, let
--   $$A=\min\{c_e+c_f : e,f\in\delta(v_1),\ e\ne f\},\qquad B=\min\Big\{\sum_{e\in T}c_e : T\text{ a spanning tree of } G\setminus v_1\Big\}.$$
--   The **1-tree bound** is $A+B$.
--
--   **Formalization Note** Both minima are taken in `EReal` and equal $+\infty$ when their sets are empty (fewer than two edges at $v_1$, or $G\setminus v_1$ disconnected), in which case $A+B=+\infty$. Neither is ever $-\infty$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, box "1-tree Bound", p. 253 (PDF p. 261)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_cut
import Definitions.Def_CombOpt_HeldKarp_Graph_IsSpanningTreeDelete

namespace CombOpt.HeldKarp

/-- **The 1-tree bound A + B.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, box
"1-tree Bound", p. 253 (PDF p. 261): "Let G = (V, E) with edge costs (c_e : e ∈ E) and let v_1 ∈ V.
Now let A = min{c_e + c_f : e, f ∈ δ(v_1), e ≠ f} and let B be the cost of a minimum spanning tree
in G \ v_1."

`G.oneTreeBound c v₁ = A + B`, where `A` is the least `c_e + c_f` over ordered pairs of distinct
edges `e, f ∈ δ(v₁)` and `B` is the least `Σ_{e ∈ T} c_e` over spanning trees `T` of `G \ v₁`.

**Formalization Note.** Both minima are taken in `EReal` over finite sets, so each is attained when
its set is nonempty and is `⊤` when it is empty (fewer than two edges in `δ(v₁)`, or `G \ v₁` has no
spanning tree); then `A + B = ⊤`. Neither minimum is ever `⊥`, so the sum is the book's. -/
noncomputable def Graph.oneTreeBound {V E : Type*} [Fintype E] (G : Graph V E) (c : E → ℝ)
    (v₁ : V) : EReal :=
  (⨅ (p : E × E) (_ : p.1 ≠ p.2 ∧ p.1 ∈ G.cut {v₁} ∧ p.2 ∈ G.cut {v₁}),
      ((c p.1 + c p.2 : ℝ) : EReal)) +
  ⨅ (T : Finset E) (_ : G.IsSpanningTreeDelete v₁ T), ((∑ e ∈ T, c e : ℝ) : EReal)

end CombOpt.HeldKarp


