-- Prove2me | Definitions.Def_ProcNetStab_KWARPS
-- name    : ProcNetStab_KWARPS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:34.171121+00:00
-- url     : https://prove2.me/theorems/73bd9b00-620d-4274-bbdd-3c7d26403158
-- title:
--   $k$-WARPS (Weak Axiom of Revealed Pairwise Stability)
-- statement:
--   Let $g$ be the observed network, $L : V \to T$ a type map and $k \in \mathbb N$. The network $g$ satisfies **$k$-WARPS** if for all nodes $i$ and $j$ there is no pair of distinct nodes $i', j'$ that is not linked, $i'j' \notin g$, such that
--   $$
--   (i, g) \simeq_k (i', g + i'j') \qquad\text{and}\qquad (j, g) \simeq_k (j', g + i'j') .
--   $$
--
--   In words: no missing link $i'j'$ would, once added, make each of its endpoints look locally like some agent of the observed network.
--
--   **Formalization Note** The nodes $i$ and $j$ are arbitrary: they need not be linked and may coincide.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 4.1, p.12 (= Definition A.3, p.OA-1)

import Mathlib
import Definitions.Def_ProcNetStab_KIso

namespace ProcNetStab

/-- **`k`-WARPS**, the Weak Axiom of Revealed Pairwise Stability (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), Definition 4.1, p.12, restated as Definition A.3,
p.OA-1): for all pairs of nodes `i` and `j`, there is no pair `i', j'` that is not linked,
`i'j' ∉ g`, such that `(i, g) ≃k (i', g + i'j')` and `(j, g) ≃k (j', g + i'j')`.

**Formalization Note** `i` and `j` are arbitrary nodes: they need not be linked and may coincide.
The non-link `i'j'` consists of distinct nodes. -/
def KWARPS {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ ∃ i j i' j' : V, i' ≠ j' ∧ ¬ g.Adj i' j' ∧
    KIso L g k i g i' (addLink g i' j') ∧ KIso L g k j g j' (addLink g i' j')

end ProcNetStab


