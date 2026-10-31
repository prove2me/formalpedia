-- Prove2me | Definitions.Def_DistributionFreeInventory_TwoLocation_Hierarchy
-- name    : DistributionFreeInventory_TwoLocation_Hierarchy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:29:48.807887+00:00
-- url     : https://prove2.me/theorems/e06604a9-1f8b-40bc-a8e8-883326fd1d09
-- title:
--   Nested partitions, fulfillment costs and marginal increments
-- statement:
--   A nested partition of $n>0$ locations has $L>0$ levels. Every level partitions all locations into nonempty disjoint clusters; level zero consists of singletons, the final level is the single cluster of all locations, and each cluster is contained in a cluster at the next level. Cluster counts strictly decrease between levels. The one-location, one-level case is included.
--
--   Positive cluster costs increase non-strictly toward the root, whose cost is at most $p+h$. Shipment between locations uses their first common cluster's cost. For a non-root cluster $I$, $\eta_{\ell,I}$ is its parent's cost minus its own; at the root it is $p+h$ minus the root cost. The independently defined expression is
--   $$h\sum_i(y_i-d_i)+\sum_i s_{0,i}d_i+\sum_{\ell=0}^{L-1}\sum_{I\in\mathcal P_\ell}\eta_{\ell,I}\max\{\sum_{i\in I}(d_i-y_i),0\}.$$
--
--   **Formalization Note** Clusters are finite subsets rather than numbered rows of assignment matrices. A finite sum selects the unique containing parent, and the least common level is a natural-number infimum over a nonempty set. Partitions are defined separately from their costs and the recourse problem. Values of the sequence of partitions and costs beyond $L-1$ are unused.
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, §2, Assumption 1, printed pp. 7–8 (PDF 7–8); equation (5), p. 10 (PDF 10)

import Definitions.Def_DistributionFreeInventory_TwoLocation_Flow
open scoped BigOperators
noncomputable section

namespace DistributionFreeInventory.TwoLocation

/-- A finite nested partition, independent of costs or the recourse formula. -/
structure NestedPartition (n : ℕ) where
  n_pos : 0 < n
  levels : ℕ
  levels_pos : 0 < levels
  parts : ℕ → Finset (Finset (Fin n))
  nonempty_parts : ∀ l < levels, ∀ I ∈ parts l, I.Nonempty
  cover : ∀ l < levels, ∀ i : Fin n, ∃ I ∈ parts l, i ∈ I
  disjoint : ∀ l < levels, ∀ I ∈ parts l, ∀ J ∈ parts l, I ≠ J → Disjoint I J
  base : parts 0 = Finset.univ.image (fun i : Fin n => {i})
  root : parts (levels - 1) = {Finset.univ}
  nested : ∀ l, l + 1 < levels → ∀ I ∈ parts l, ∃ J ∈ parts (l + 1), I ⊆ J
  decreasing : ∀ l, l + 1 < levels → (parts (l + 1)).card < (parts l).card

/-- Source Assumption 1: positive costs, non-strict increase along every branch. -/
def NestedCosts {n : ℕ} (H : NestedPartition n)
    (c : ℕ → Finset (Fin n) → ℝ) (h p : ℝ) : Prop :=
  (∀ l < H.levels, ∀ I ∈ H.parts l, 0 < c l I) ∧
  (∀ l, l + 1 < H.levels → ∀ I ∈ H.parts l, ∀ J ∈ H.parts (l + 1),
    I ⊆ J → c l I ≤ c (l + 1) J) ∧
  c (H.levels - 1) Finset.univ ≤ p + h

/-- Least level with a common cluster (the root ensures this set is nonempty). -/
def firstCommon {n : ℕ} (H : NestedPartition n) (i j : Fin n) : ℕ :=
  sInf {l | l < H.levels ∧ ∃ I ∈ H.parts l, i ∈ I ∧ j ∈ I}

/-- The unique first common cluster sets the actual shipment cost. -/
def nestedMatrix {n : ℕ} (H : NestedPartition n)
    (c : ℕ → Finset (Fin n) → ℝ) (i j : Fin n) : ℝ :=
  ∑ I ∈ H.parts (firstCommon H i j),
    if i ∈ I ∧ j ∈ I then c (firstCommon H i j) I else 0

/-- The sum picks the unique parent of a nonempty cluster. -/
def parentCost {n : ℕ} (H : NestedPartition n)
    (c : ℕ → Finset (Fin n) → ℝ) (l : ℕ) (I : Finset (Fin n)) : ℝ :=
  ∑ J ∈ H.parts (l + 1), if I ⊆ J then c (l + 1) J else 0

/-- Marginal cost increments, with a separate root boundary. -/
def eta {n : ℕ} (H : NestedPartition n) (c : ℕ → Finset (Fin n) → ℝ)
    (h p : ℝ) (l : ℕ) (I : Finset (Fin n)) : ℝ :=
  if l + 1 < H.levels then parentCost H c l I - c l I else p + h - c l I

/-- The right side of (5), independently of the flow optimum. -/
def nestedExpression {n : ℕ} (H : NestedPartition n)
    (c : ℕ → Finset (Fin n) → ℝ) (h p : ℝ) (y d : Fin n → ℝ) : ℝ :=
  h * (∑ i, (y i - d i)) + (∑ i, c 0 {i} * d i) +
    ∑ l ∈ Finset.range H.levels, ∑ I ∈ H.parts l,
      eta H c h p l I * max ((∑ i ∈ I, d i) - ∑ i ∈ I, y i) 0

end DistributionFreeInventory.TwoLocation


