-- Prove2me | Definitions.Def_ProcNetStab_KAnonymous
-- name    : ProcNetStab_KAnonymous
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:38.805345+00:00
-- url     : https://prove2.me/theorems/87916475-380b-4d9b-9e1c-cc34a8e6527e
-- title:
--   $k$-anonymity of a preference profile
-- statement:
--   Let $g$ be the observed network, $k \in \mathbb N$ and $L : V \to T$ a type map. A preference profile $\succeq$ satisfies **$k$-anonymity** if for all agents $i, i'$, all nodes $j, j'$ and all networks $h, h'$:
--   $$
--   (i, h) \simeq_k (i', h') \ \text{and}\ (i, h - ij) \simeq_k (i', h' - i'j')
--   $$
--   imply that either
--
--   1. $h \succeq_i h - ij$ and $h' \succeq_{i'} h' - i'j'$, or
--   2. $h \prec_i h - ij$ and $h' \prec_{i'} h' - i'j'$.
--
--   Agents that are $k$-isomorphic before and after a link change have the same incentive to keep that link. Since $\simeq_k$ only relates networks adjacent to $g$, the restriction concerns only comparisons near the observed network.
--
--   **Formalization Note** The networks $h, h'$ (written $g, g'$ in the paper) are universally quantified; the observed network $g$ enters only through the adjacency clause of $\simeq_k$. $h - ij$ is edge deletion, which leaves $h$ unchanged when $ij \notin h$.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 3.9, p.10 (= Definition A.2, p.OA-1)

import Mathlib
import Definitions.Def_ProcNetStab_KIso
import Definitions.Def_ProcNetStab_IsWeakOrder

namespace ProcNetStab

/-- **`k`-anonymity** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025),
Definition 3.9, p.10, restated as Definition A.2, p.OA-1): a preference profile `⪰` satisfies
`k`-anonymity if `(i, h) ≃k (i', h')` and `(i, h − ij) ≃k (i', h' − i'j')` imply that either
(i) `h ⪰_i h − ij` and `h' ⪰_{i'} h' − i'j'`, or (ii) `h ≺_i h − ij` and `h' ≺_{i'} h' − i'j'`,
for all agents `i` and `i'`.

**Formalization Note** The networks `h, h'` (the paper's bound `g, g'`) and the nodes
`i, i', j, j'` are all universally quantified; the observed network `g` enters only through the
adjacency clause inside `≃k` (`KIso`). `h − ij` is `delLink h i j`, a no-op when `ij ∉ h`. -/
def KAnonymous {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (pref : V → SimpleGraph V → SimpleGraph V → Prop) : Prop :=
  ∀ (i i' j j' : V) (h h' : SimpleGraph V),
    KIso L g k i h i' h' → KIso L g k i (delLink h i j) i' (delLink h' i' j') →
      (pref i h (delLink h i j) ∧ pref i' h' (delLink h' i' j')) ∨
        (strictPart (pref i) (delLink h i j) h ∧ strictPart (pref i') (delLink h' i' j') h')

end ProcNetStab


