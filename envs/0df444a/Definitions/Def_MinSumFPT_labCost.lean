-- Prove2me | Definitions.Def_MinSumFPT_labCost
-- name    : MinSumFPT_labCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:53.391669+00:00
-- url     : https://prove2.me/theorems/d207de1d-d28b-4edf-b4b8-6a2b4b2233ad
-- title:
--   Clusterings as labellings, $\mathrm{cost}$, $\mathrm{OPT}_k$ and MAX $k$-CUT
-- statement:
--   Let $A=\{0,\dots,n-1\}$ carry a distance function $d$. A clustering of $A$ into $k$ clusters is given by a labelling $\sigma:A\to\{0,\dots,k-1\}$, the cluster with label $i$ being $C_i=\{x:\sigma(x)=i\}$. Its **k-minsum cost** is
--
--   $$
--   \mathrm{cost}(\sigma)=\sum_{i=0}^{k-1}\ \sum_{x,y\in C_i} d(x,y),
--   $$
--
--   the sum running over ordered pairs. The **optimal k-minsum cost** is $\mathrm{OPT}_k(d)=\min_\sigma \mathrm{cost}(\sigma)$ over all labellings. The **MAX k-CUT value** of $\sigma$ is $\mathrm{cut}(\sigma)=\sum_{x,y:\ \sigma(x)\ne\sigma(y)} d(x,y)$, and $\mathrm{maxcut}_k(d)=\max_\sigma \mathrm{cut}(\sigma)$.
--
--   These are the two objectives of the paper: k-minsum clustering (§1) and its complement, metric MAX k-CUT (§2.6); $\mathrm{cost}(\sigma)+\mathrm{cut}(\sigma)=\sum_{x,y}d(x,y)$.
--
--   **Formalization Note** Clusters may be empty. For $1\le k\le n$ and nonnegative $d$ the minimum over all labellings equals the minimum over partitions into exactly $k$ nonempty clusters, which is the paper's $\mathrm{OPT}$. The cluster cost is the published `MinSumClust.cost`.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §1, p.1 (cost(𝒞)) and §2.6, p.38 (metric MAX k-CUT)

import Mathlib
import Definitions.Def_MinSumClust_cost

namespace MinSumFPT

/-!
# Clusterings as labellings; the k-minsum objective and the MAX k-CUT objective

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §1, p.1 (cost(𝒞) = ∑_{i=1}^k ∑_{x,y∈C_i} d(x,y), the k-minsum problem) and §2.6, p.38
(metric MAX k-CUT: maximize the sum of inter-cluster distances).

This module bundles the tightly coupled objects `clusterOf`, `labCost`, `optCost`, `cutVal`,
`maxCut`.

**Formalization Note.** The points are `Fin n`; a clustering into `k` clusters is a labelling
`σ : Fin n → Fin k` (0-based labels; the paper's `C_1, …, C_k` are `clusterOf σ 0, …,
clusterOf σ (k − 1)`), and empty clusters are allowed. Costs count **ordered** pairs, the diagonal
included, through the published `MinSumClust.cost` (as the paper's ∑_{x,y∈C}); `cutVal` counts
ordered pairs in different clusters. `optCost d k` is the infimum over all labellings, a minimum over
a finite nonempty type when `k ≥ 1` (every statement assumes `k ≥ 1`); for `k ≤ n` it equals the
minimum over partitions into exactly `k` nonempty clusters. -/

/-- The cluster with label `i` of the labelling `σ`. -/
def clusterOf {n k : ℕ} (σ : Fin n → Fin k) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun x => σ x = i)

/-- The k-minsum cost `∑_i ∑_{x,y ∈ C_i} d(x, y)` of the labelling `σ`. -/
noncomputable def labCost {n k : ℕ} (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) : ℝ :=
  ∑ i, MinSumClust.cost d (clusterOf σ i)

/-- The optimal k-minsum cost `OPT_k(d)`: the least cost of a labelling into `k` labels. -/
noncomputable def optCost {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) : ℝ :=
  ⨅ σ : Fin n → Fin k, labCost d σ

/-- The MAX k-CUT value `∑_{x,y : σ x ≠ σ y} d(x, y)` of the labelling `σ` (ordered pairs). -/
noncomputable def cutVal {n k : ℕ} (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) : ℝ :=
  ∑ x, ∑ y, if σ x ≠ σ y then d x y else 0

/-- The optimal MAX k-CUT value: the largest cut value of a labelling into `k` labels. -/
noncomputable def maxCut {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) : ℝ :=
  ⨆ σ : Fin n → Fin k, cutVal d σ

end MinSumFPT


