-- Prove2me | Definitions.Def_MetricMatchingDistortion_IsClusterCompletion
-- name    : MetricMatchingDistortion_IsClusterCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:40.618303+00:00
-- url     : https://prove2.me/theorems/db02a6ed-fde7-43dd-a4c1-51820b402492
-- title:
--   The completion guarantee (3) of Lemma 3.1
-- statement:
--   A map $\mathrm{complete}(X,\mathcal P)$, taking a partial fractional matching and a partition (never the distances), is a **cluster completion** if for every partial fractional matching $X$ with unmatched mass $k$ and every balanced partition $\mathcal P$, $M=\mathrm{complete}(X,\mathcal P)$ is a perfect fractional matching and, for every $d$ nonnegative on agent–item pairs,
--   $$\mathrm{cost}(M,d)\le \mathrm{cost}(X,d)+\sum_j\min\{k,|A_j|\}\,w_j\le\mathrm{cost}(X,d)+k\,W(\mathcal P,d).$$
--   Algorithm 1 (ClusterCompletion) has this guarantee (Lemma 3.1).
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Lemma 3.1, p.13 (PDF p.15), Equation (3)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_IsBalanced

namespace MetricMatchingDistortion

/-- **The completion guarantee of Lemma 3.1.** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Lemma 3.1, p.13 (PDF p.15): "Given a
partial fractional matching X with unmatched mass k and a balanced partition P, Algorithm 1 uses
only X and the cluster memberships to return a perfect fractional matching M satisfying
cost(M, d) ≤ cost(X, d) + ∑_j min{k, |Aj|} wj ≤ cost(X, d) + kW(P, d) (3) for every d ∈ ρ(σ)."

`IsClusterCompletion complete` says that the map `complete`, which sees only the partial matching
`X` and the labelling `c` (never the distances), turns every partial fractional matching `X` and
every balanced labelling `c` into a perfect fractional matching `M = complete X c` such that, with
`k = n − ∑ X`, both inequalities of (3) hold for every `d` that is nonnegative on agent–item pairs.

**Formalization Note.** Algorithm 1 (ClusterCompletion, p.13) chooses its augmenting paths freely;
the guarantee is stated for a map, of which any run of Algorithm 1 with a fixed path choice is an
instance. The class of `d` (nonnegative on agent–item pairs) contains every `d ∈ ρ(σ)`. -/
def IsClusterCompletion {n : ℕ}
    (complete : (Fin n → Fin n → ℝ) → (Fin n ⊕ Fin n → Fin n) → (Fin n → Fin n → ℝ)) : Prop :=
  ∀ X c, IsPartialFractionalMatching X → IsBalanced c →
    IsPerfectFractionalMatching (complete X c) ∧
      ∀ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, (∀ a b, 0 ≤ d (Sum.inl a) (Sum.inr b)) →
        fracCost (complete X c) d ≤
            fracCost X d + ∑ j, min (unmatchedMass X) ((clusterAgents c j).card : ℝ) *
              clusterWeight c d j ∧
          ∑ j, min (unmatchedMass X) ((clusterAgents c j).card : ℝ) * clusterWeight c d j ≤
            unmatchedMass X * partitionCost c d

end MetricMatchingDistortion


