-- Prove2me | Definitions.Def_ProcNetStab_KWARPSAlt
-- name    : ProcNetStab_KWARPSAlt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:38.944744+00:00
-- url     : https://prove2.me/theorems/12371559-f3a0-46fa-9019-da2bd4654cb1
-- title:
--   Alternate form of $k$-WARPS (Definition A.4)
-- statement:
--   Let $g$ be the observed network, $L : V \to T$ a type map and $k \in \mathbb N$. The network $g$ satisfies the **alternate form of $k$-WARPS** if for all links $ix \in g$ and $jy \in g$ there is no non-link $i'j' \notin g$ such that
--
--   1. $(i, g) \simeq_k (i', g + i'j')$ and $(i, g - ix) \simeq_k (i', g)$, and
--   2. $(j, g) \simeq_k (j', g + i'j')$ and $(j, g - jy) \simeq_k (j', g)$.
--
--   This is the form of the axiom used in the paper's proofs.
--
--   **Formalization Note** The non-link $i'j'$ consists of distinct nodes.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition A.4, p.OA-1 (PDF p.30)

import Mathlib
import Definitions.Def_ProcNetStab_KIso

namespace ProcNetStab

/-- The **alternate form of `k`-WARPS** (Chiong, Qi, *Stability of Procurement Networks* (authors'
manuscript, 2025), Definition A.4, p.OA-1): for all pairs of links `ix ∈ g` and `jy ∈ g`, there is
no non-link `i'j' ∉ g` such that
1. `(i, g) ≃k (i', g + i'j')` and `(i, g − ix) ≃k (i', g)`, and
2. `(j, g) ≃k (j', g + i'j')` and `(j, g − jy) ≃k (j', g)`.

**Formalization Note** The non-link `i'j'` consists of distinct nodes. -/
def KWARPSAlt {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ ∃ i x j y i' j' : V, g.Adj i x ∧ g.Adj j y ∧ i' ≠ j' ∧ ¬ g.Adj i' j' ∧
    (KIso L g k i g i' (addLink g i' j') ∧ KIso L g k i (delLink g i x) i' g) ∧
    (KIso L g k j g j' (addLink g i' j') ∧ KIso L g k j (delLink g j y) j' g)

end ProcNetStab


