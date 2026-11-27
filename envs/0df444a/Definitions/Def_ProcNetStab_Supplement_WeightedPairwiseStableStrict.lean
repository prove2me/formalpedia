-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedPairwiseStableStrict
-- name    : ProcNetStab_Supplement_WeightedPairwiseStableStrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:55:29.197384+00:00
-- url     : https://prove2.me/theorems/c0f92103-b2c2-4429-b53d-254ce6e71860
-- title:
--   Weighted pairwise stability, the strict reading used in Appendix A.7.1
-- statement:
--   Let $g = (N, W)$ be a weighted network and $u = (u_a)_{a \in N}$ a profile of utility functions on all weighted networks. Call $g$ **strictly weighted pairwise stable** with respect to $u$ if for every ordered pair of distinct nodes $i \ne j$:
--
--   1. for all $x \in [0, W_{ij}]$, $\; u_i(g) \ge u_i((x, g_{-ij}))$ (condition 1 of Definition 5.1);
--   2. for all $x \in (W_{ij}, 1]$, $\; u_i(g) > u_i((x, g_{-ij}))$ or $u_j(g) > u_j((x, g_{-ij}))$.
--
--   Condition 2 is how the paper's proof of necessity in Theorem 2 (Appendix A.7.1) reads Definition 5.1: "for all $x \in (W_{i'j'}, 1]$, either (1) $u_{i'}(g) > u_{i'}((x, g_{-i'j'}))$ or (2) $u_{j'}(g) > u_{j'}((x, g_{-i'j'}))$". It is the weighted analogue of condition 2 of Definition 3.1, "$g \succ_i g + ij$ or $g \succ_j g + ij$": every increase of a weight is strictly refused by at least one endpoint.
--
--   **Formalization Note** It differs from Definition 5.1 as printed only in condition 2. The mission states the two readings separately and never mixes them.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Appendix A.7.1, p.OA-7 (PDF 36), reading of Definition 5.1, p.18

import Mathlib
import Definitions.Def_ProcNetStab_Supplement_WeightedNet

namespace ProcNetStab.Supplement

/-- **Weighted pairwise stability, the reading used in the proof of Theorem 2** (Chiong, Qi,
*Stability of Procurement Networks* (authors' manuscript, 2025), Appendix A.7.1, p.OA-7, PDF 36:
"for all x ∈ (W_{i′j′}, 1], either (1) u_{i′}(g) > u_{i′}((x, g_{−i′j′})) or
(2) u_{j′}(g) > u_{j′}((x, g_{−i′j′}))"; the weighted analogue of Definition 3.1's
"g ≻_i g + ij or g ≻_j g + ij"): for all pairs of nodes `i ≠ j`,
1. for all `x ∈ [0, W i j]`, `u_i(g) ≥ u_i((x, g_{-ij}))` (as in Definition 5.1);
2. for all `x ∈ (W i j, 1]`, `u_i(g) > u_i((x, g_{-ij}))` or `u_j(g) > u_j((x, g_{-ij}))`.

**Formalization Note** Same conventions as `WeightedPairwiseStable`; only condition 2 differs. -/
def WeightedPairwiseStableStrict {V : Type*} (g : WeightedNet V) (u : V → WeightedNet V → ℝ) :
    Prop :=
  ∀ i j : V, i ≠ j →
    (∀ x ∈ Set.Icc (0 : ℝ) (g.W i j), u i (setWeight g i j x) ≤ u i g) ∧
      ∀ x ∈ Set.Ioc (g.W i j) 1,
        u i (setWeight g i j x) < u i g ∨ u j (setWeight g i j x) < u j g

end ProcNetStab.Supplement


