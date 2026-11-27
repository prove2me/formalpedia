-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedKAnonymous
-- name    : ProcNetStab_Supplement_WeightedKAnonymous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:56:08.681329+00:00
-- url     : https://prove2.me/theorems/bfe28945-8afd-4c2e-81bd-046585b87145
-- title:
--   Weighted $k$-anonymity (Definition 5.2)
-- statement:
--   Let $g$ be the observed weighted network, $k \in \mathbb N$, and let every node carry a type through $L : V \to T$. For weighted networks the $k$-isomorphic relation is that of the unweighted networks: $(i, h) \simeq_k (i', h')$ means $(i, B(h)) \simeq_k (i', B(h'))$, where both $B(h)$ and $B(h')$ must be adjacent to $B(g)$.
--
--   A profile of utility functions $u$ satisfies **weighted $k$-anonymity** if for all agents $i, i', j, j'$, all weighted networks $h, h'$ and all weights $0 \le x < y \le 1$: whenever
--   $$
--   (i, h) \simeq_k (i', h') \quad\text{and}\quad (i, h - ij) \simeq_k (i', h' - i'j'),
--   $$
--   then
--   $$
--   u_i((x, h_{-ij})) > u_i((y, h_{-ij})) \implies u_{i'}((x, h'_{-i'j'})) > u_{i'}((y, h'_{-i'j'})).
--   $$
--   Here $h - ij$ is the network $(0, h_{-ij})$ with the link $ij$ removed.
--
--   Agents in the same local position have the same strict incentives to raise or lower the weight of a link by the same amount. Taking $x = 0$, $y = 1$ recovers the second part of Definition 3.9.
--
--   **Formalization Note** The relation $\simeq_k$ is the base mission's `ProcNetStab.KIso` applied to $B(\cdot)$, with $B(g)$ as the observed network. The networks $h, h'$ (the paper's bound $g, g'$) are universally quantified. Only the strict implication is imposed, as printed; the weak half, which the paper calls optional, is not added.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 5.2, p.19, with the weighted k-isomorphism of §5.1, p.19

import Mathlib
import Definitions.Def_ProcNetStab_KIso
import Definitions.Def_ProcNetStab_Supplement_WeightedNet

namespace ProcNetStab.Supplement

/-- **Weighted `k`-anonymity** (Chiong, Qi, *Stability of Procurement Networks* (authors'
manuscript, 2025), Definition 5.2, p.19, with the weighted `≃k` of §5.1, p.19): a utility profile
`u` satisfies weighted `k`-anonymity if whenever `(i, h) ≃k (i', h')` and
`(i, h − ij) ≃k (i', h' − i'j')`, then
`u_i((x, h_{-ij})) > u_i((y, h_{-ij}))` implies `u_{i'}((x, h'_{-i'j'})) > u_{i'}((y, h'_{-i'j'}))`
for all `y > x ≥ 0`.

**Formalization Note** The weighted relation `≃k` is the base mission's `KIso` applied to the
unweighted networks `B(·)` (`support`), with `B(g)` of the observed weighted network `g` in its
adjacency clause (§5.1). The networks `h, h'` (the paper's bound `g, g'`) and the nodes
`i, i', j, j'` are universally quantified. `h − ij` is the weight-`0` network `(0, h_{-ij})`.
The weights satisfy `0 ≤ x < y ≤ 1`. Only the strict implication is imposed, as printed; the weak
half the paper calls optional is not added. -/
def WeightedKAnonymous {V T : Type*} (L : V → T) (g : WeightedNet V) (k : ℕ)
    (u : V → WeightedNet V → ℝ) : Prop :=
  ∀ (i i' j j' : V) (h h' : WeightedNet V) (x y : ℝ), 0 ≤ x → x < y → y ≤ 1 →
    KIso L (support g) k i (support h) i' (support h') →
    KIso L (support g) k i (support (setWeight h i j 0)) i' (support (setWeight h' i' j' 0)) →
    u i (setWeight h i j y) < u i (setWeight h i j x) →
      u i' (setWeight h' i' j' y) < u i' (setWeight h' i' j' x)

end ProcNetStab.Supplement


