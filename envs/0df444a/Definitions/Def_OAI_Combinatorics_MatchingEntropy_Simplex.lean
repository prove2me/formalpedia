-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
-- name    : OAI_Combinatorics_MatchingEntropy_Simplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:26:33.179707+00:00
-- url     : https://prove2.me/theorems/89bdb984-4b25-4f89-9199-2eb543de09f8
-- title:
--   The probability simplex is convex and contains every point mass
-- statement:
--   Let $I$ be a finite index set and let
--   $$
--   \Delta(I)=\Big\{w\in\mathbb{R}^I:\ w_i\ge0\ \text{for all } i\in I,\ \ \sum_{i\in I}w_i=1\Big\}
--   $$
--   be the probability simplex of real weight vectors on $I$. This module records two basic facts.
--
--   1. *Convexity.* $\Delta(I)$ is a convex subset of $\mathbb{R}^I$: if $w,w'\in\Delta(I)$ and $a,b\ge0$ with $a+b=1$, then $aw+bw'\in\Delta(I)$.
--   2. *Point masses.* For every $i\in I$, the unit vector $\delta_i$, with $\delta_i(i)=1$ and $\delta_i(j)=0$ for $j\neq i$, belongs to $\Delta(I)$.
--
--   Together these say that $\Delta(I)$ is a convex set containing all point masses, so its image under any linear map is convex and contains the images of the point masses, hence their convex hull. Applied to the map sending a law on perfect matchings to its vector of edge marginals, this shows that every point of the convex hull of the matching indicator vectors is the marginal vector of some probability law.
--
--   **Formalization Note** The lemmas are `convex_probabilitySimplex` and `single_mem_probabilitySimplex`; the point mass is `Pi.single i 1`, which needs decidable equality on $I$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Simplex.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Simplex.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model

namespace OAI

noncomputable section

open scoped BigOperators

universe uIndex

namespace MatchingEntropyBounds

theorem convex_probabilitySimplex (Index : Type uIndex) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem single_mem_probabilitySimplex {Index : Type uIndex} [Fintype Index]
    [DecidableEq Index] (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index := by
  constructor
  · intro other
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

end MatchingEntropyBounds

end

end OAI


