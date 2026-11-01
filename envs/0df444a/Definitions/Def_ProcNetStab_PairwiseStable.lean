-- Prove2me | Definitions.Def_ProcNetStab_PairwiseStable
-- name    : ProcNetStab_PairwiseStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:00.451438+00:00
-- url     : https://prove2.me/theorems/f36cb538-9d8c-4b23-95a6-17f9731e1b96
-- title:
--   Pairwise stability (Jackson–Wolinsky)
-- statement:
--   Let $g$ be a network on $V$ and $\succeq = (\succeq_a)_{a \in V}$ a profile of preference relations over networks. The network $g$ is **pairwise stable** with respect to $\succeq$ if
--
--   1. for all links $ij \in g$: $g \succeq_i g - ij$ and $g \succeq_j g - ij$;
--   2. for all non-links $ij \notin g$: $g \succ_i g + ij$ or $g \succ_j g + ij$.
--
--   No agent wants to dissolve an existing link, and for every missing link at least one of its endpoints strictly prefers not to form it.
--
--   **Formalization Note** A profile is `pref : V → SimpleGraph V → SimpleGraph V → Prop`, with `pref a x y` read as $x \succeq_a y$. A non-link is a pair of distinct, unlinked nodes.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 3.1, p.7

import Mathlib
import Definitions.Def_ProcNetStab_IsAdjacentNet
import Definitions.Def_ProcNetStab_IsWeakOrder

namespace ProcNetStab

/-- **Pairwise stability** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), Definition 3.1, p.7; Jackson–Wolinsky 1996): the network `g` is pairwise stable with
respect to the preference profile `pref` if
1. for all `ij ∈ g`, `g ⪰_i g − ij` and `g ⪰_j g − ij`, and
2. for all `ij ∉ g`, `g ≻_i g + ij` or `g ≻_j g + ij`.

**Formalization Note** A profile is `pref : V → SimpleGraph V → SimpleGraph V → Prop`, with
`pref a x y` read as `x ⪰_a y`. A non-link `ij ∉ g` is a pair of distinct nodes with
`¬ g.Adj i j`. -/
def PairwiseStable {V : Type*} (g : SimpleGraph V)
    (pref : V → SimpleGraph V → SimpleGraph V → Prop) : Prop :=
  (∀ i j : V, g.Adj i j → pref i g (delLink g i j) ∧ pref j g (delLink g i j)) ∧
    ∀ i j : V, i ≠ j → ¬ g.Adj i j →
      strictPart (pref i) g (addLink g i j) ∨ strictPart (pref j) g (addLink g i j)

end ProcNetStab


