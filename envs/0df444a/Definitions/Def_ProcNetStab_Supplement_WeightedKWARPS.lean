-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedKWARPS
-- name    : ProcNetStab_Supplement_WeightedKWARPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:56:44.500452+00:00
-- url     : https://prove2.me/theorems/71c1c843-c514-4180-ada4-f3fadb68865b
-- title:
--   Weighted-$k$-WARPS (Definition 5.3)
-- statement:
--   Let $g = (N, W)$ be the observed weighted network, $k \in \mathbb N$ and $L : V \to T$ a type map. The network $g$ satisfies **Weighted-$k$-WARPS** if for all $W_{ij} > 0$ there do not exist distinct nodes $i', j'$ with $W_{i'j'} < W_{ij}$ such that
--
--   1. $(i, g) \simeq_k (i', g + i'j'\,\mathbb 1(W_{i'j'} = 0))$, and
--   2. $(j, g) \simeq_k (j', g + i'j'\,\mathbb 1(W_{i'j'} = 0))$.
--
--   Here $\simeq_k$ is the $k$-isomorphic relation on unweighted networks $B(\cdot)$ with observed network $B(g)$, and $g + i'j'\,\mathbb 1(W_{i'j'} = 0)$ is $B(g) + i'j'$ when $W_{i'j'} = 0$ and $B(g)$ otherwise.
--
--   The condition forbids a link $ij$ whose endpoints look locally like the endpoints of a pair $i'j'$ of strictly lower weight; it is the weighted analogue of $k$-WARPS (Definition 4.1).
--
--   **Formalization Note** The witnesses $i, j$ are the endpoints of a link ($W_{ij} > 0$), as printed; this differs from Definition 4.1, where $i$ and $j$ are arbitrary nodes. The pair $i'j'$ may be linked or not.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 5.3, p.19, with the weighted k-isomorphism of §5.1, p.19

import Mathlib
import Definitions.Def_ProcNetStab_KIso
import Definitions.Def_ProcNetStab_Supplement_WeightedNet

namespace ProcNetStab.Supplement

open Classical in
/-- **Weighted-`k`-WARPS** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), Definition 5.3, p.19, with the weighted `≃k` of §5.1, p.19): the weighted network `g`
satisfies Weighted-`k`-WARPS if for all `W i j > 0` there is no pair `i'j'` with
`W i' j' < W i j` such that
1. `(i, g) ≃k (i', g + i'j' 1(W i' j' = 0))` and
2. `(j, g) ≃k (j', g + i'j' 1(W i' j' = 0))`.

**Formalization Note** `≃k` is the base mission's `KIso` on unweighted networks `B(·)`
(`support`), with observed network `B(g)`. `g + i'j' 1(W i' j' = 0)` is `B(g) + i'j'` when
`W i' j' = 0` and `B(g)` otherwise. The witnesses `i, j` are the endpoints of a link
(`W i j > 0`); the pair `i'j'` consists of distinct nodes and may be linked or not. -/
def WeightedKWARPS {V T : Type*} (L : V → T) (g : WeightedNet V) (k : ℕ) : Prop :=
  ¬ ∃ i j i' j' : V, 0 < g.W i j ∧ i' ≠ j' ∧ g.W i' j' < g.W i j ∧
    KIso L (support g) k i (support g) i'
      (if g.W i' j' = 0 then addLink (support g) i' j' else support g) ∧
    KIso L (support g) k j (support g) j'
      (if g.W i' j' = 0 then addLink (support g) i' j' else support g)

end ProcNetStab.Supplement


