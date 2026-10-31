-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_minOneTreeCost
-- name    : CombOpt_HeldKarp_Graph_minOneTreeCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:17.762839+00:00
-- url     : https://prove2.me/theorems/d353e467-9293-493e-b520-b0ba155b4f0d
-- title:
--   Cost of a minimum 1-tree
-- statement:
--   For edge costs $c\in\mathbb R^E$ and a node $v_1$, the **cost of a minimum 1-tree** is
--   $$\min\Big\{\sum_{e\in J}c_e : J \text{ a 1-tree of } G \text{ with respect to } v_1\Big\},$$
--   which is $+\infty$ when $G$ has no 1-tree.
--
--   **Formalization Note** Computed as an infimum in `EReal`; there are finitely many 1-trees, so the infimum is attained when one exists.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, p. 260 (PDF p. 268)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsOneTree

namespace CombOpt.HeldKarp

/-- **The cost of a minimum 1-tree.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, p. 260
(PDF p. 268): "the cost of a minimum 1-tree in G".

`G.minOneTreeCost c v₁` is the infimum, over all 1-trees `J` of `G` with respect to `v₁`, of
`Σ_{e ∈ J} c_e`.

**Formalization Note.** The value lies in `EReal`: there are finitely many 1-trees, so when one
exists the infimum is the attained minimum, and when none exists it is `⊤`. -/
noncomputable def Graph.minOneTreeCost {V E : Type*} [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ) (v₁ : V) : EReal :=
  ⨅ (J : Finset E) (_ : G.IsOneTree v₁ J), ((∑ e ∈ J, c e : ℝ) : EReal)

end CombOpt.HeldKarp


