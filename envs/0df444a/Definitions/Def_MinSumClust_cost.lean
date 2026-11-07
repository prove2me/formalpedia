-- Prove2me | Definitions.Def_MinSumClust_cost
-- name    : MinSumClust_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:36.094886+00:00
-- url     : https://prove2.me/theorems/97eb8cc3-2ea5-4c68-9b14-3d1316b84719
-- title:
--   Distances $d(i,S)$, $d(A,B)$ and the cluster cost $\mathrm{cost}(S)$
-- statement:
--   Let $D$ be a set of clients and $d : D\times D\to\mathbb R$ a distance function. For a client $i$ and finite sets $S, A, B\subseteq D$ the paper writes
--
--   $$d(i,S)=\sum_{j\in S} d(i,j),\qquad d(A,B)=\sum_{i\in A} d(i,B),\qquad \mathrm{cost}(S)=d(S,S)=\sum_{i\in S}\sum_{j\in S} d(i,j).$$
--
--   The cost of a cluster is the sum of the distances over **ordered** pairs of its clients (each unordered pair counts twice, and the diagonal terms $d(i,i)$ are included). The cost of a family of clusters is the sum of their costs. These are the objective of min-sum $k$-clustering and the quantities of every statement of the mission.
--
--   **Formalization Note** The distance is any real function; metric axioms are separate hypotheses (`IsPseudometric`, `IsMetric`). Footnote 1 of the paper says that counting unordered pairs instead is irrelevant; the mission uses ordered pairs throughout, which matters for the free term $k\cdot f$ of Theorem 2.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §1, p.1 (PDF p.3), footnote 1; "Notation", p.42 (PDF p.44)

import Mathlib

namespace MinSumClust

/-- **Point-to-set distance** `d(i, S) = ∑_{j ∈ S} d(i, j)`.

Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, *A Constant Approximation for Min-sum
k-Clustering*, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §1, p.1,
and "Notation", p.42.

**Formalization Note.** The distance is any real function `d : D → D → ℝ`; the metric axioms are
hypotheses of the statements (`IsPseudometric`, `IsMetric`), never part of this definition. -/
def dist1 {D : Type*} (d : D → D → ℝ) (i : D) (S : Finset D) : ℝ :=
  ∑ j ∈ S, d i j

/-- **Set-to-set distance** `d(A, B) = ∑_{i ∈ A} d(i, B)`, "Notation", p.42 (Anand et al., STOC
2027 submission). -/
def distSet {D : Type*} (d : D → D → ℝ) (A B : Finset D) : ℝ :=
  ∑ i ∈ A, dist1 d i B

/-- **Cost of a cluster** `cost(S) = ∑_{i ∈ S} d(i, S) = ∑_{i ∈ S} ∑_{j ∈ S} d(i, j)`, §1, p.1 and
p.42 (Anand et al., STOC 2027 submission).

**Formalization Note.** The double sum runs over **ordered** pairs, including `i = j`, as in the
paper (footnote 1, p.1: unordered pairs are "irrelevant for our goals"). -/
def cost {D : Type*} (d : D → D → ℝ) (S : Finset D) : ℝ :=
  distSet d S S

end MinSumClust


