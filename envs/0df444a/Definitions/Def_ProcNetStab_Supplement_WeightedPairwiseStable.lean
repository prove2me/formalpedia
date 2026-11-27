-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedPairwiseStable
-- name    : ProcNetStab_Supplement_WeightedPairwiseStable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:55:04.564915+00:00
-- url     : https://prove2.me/theorems/b9df30c5-43db-5f2f-9718-c71a3742a94f
-- title:
--   Weighted pairwise stability (Definition 5.1, as printed)
-- statement:
--   Let $g = (N, W)$ be a weighted network and $u = (u_a)_{a \in N}$ a profile of utility functions $u_a : \mathcal G \to \mathbb R$ on the set $\mathcal G$ of all weighted networks. The network $g$ is **weighted pairwise stable** with respect to $u$ if for every ordered pair of distinct nodes $i \ne j$:
--
--   1. for all $x \in [0, W_{ij}]$, $\; u_i(g) \ge u_i((x, g_{-ij}))$;
--   2. for all $x \in [W_{ij}, 1]$, if $u_i((x, g_{-ij})) > u_i(g)$, then $u_j((x, g_{-ij})) < u_j(g)$.
--
--   No agent gains by unilaterally lowering the weight of one of its links (condition 1, which includes severing the link, $x = 0$), and an increase that benefits one endpoint strictly hurts the other (condition 2). This is the definition of Bich and Morhaim (2020) exactly as printed in the paper.
--
--   **Formalization Note** Condition 2 is the implication as printed. It holds trivially for constant utility profiles, so constant utilities make every weighted network weighted pairwise stable. The "either … or" form that the paper's proof of Theorem 2 uses (Appendix A.7.1) is the separate definition `WeightedPairwiseStableStrict`.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 5.1, p.18

import Mathlib
import Definitions.Def_ProcNetStab_Supplement_WeightedNet

namespace ProcNetStab.Supplement

/-- **Weighted pairwise stability**, as printed (Chiong, Qi, *Stability of Procurement Networks*
(authors' manuscript, 2025), Definition 5.1, p.18; Bich and Morhaim 2020): the weighted network `g`
is weighted pairwise stable with respect to the utility profile `u` if for all pairs of nodes
`i ≠ j`:
1. for all `x ∈ [0, W i j]`, `u_i(g) ≥ u_i((x, g_{-ij}))`;
2. for all `x ∈ [W i j, 1]`, if `u_i((x, g_{-ij})) > u_i(g)` then `u_j((x, g_{-ij})) < u_j(g)`.

**Formalization Note** `u : V → WeightedNet V → ℝ` assigns to each agent a utility on all
weighted networks. The pair `(i, j)` is ordered, so both endpoints are checked. Condition 2 is the
implication exactly as printed; the strict "either … or" form used in the proof of Theorem 2
(Appendix A.7.1) is the separate definition `WeightedPairwiseStableStrict`. -/
def WeightedPairwiseStable {V : Type*} (g : WeightedNet V) (u : V → WeightedNet V → ℝ) : Prop :=
  ∀ i j : V, i ≠ j →
    (∀ x ∈ Set.Icc (0 : ℝ) (g.W i j), u i (setWeight g i j x) ≤ u i g) ∧
      ∀ x ∈ Set.Icc (g.W i j) 1, u i g < u i (setWeight g i j x) →
        u j (setWeight g i j x) < u j g

end ProcNetStab.Supplement


