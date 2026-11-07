-- Prove2me | Definitions.Def_MinSumClust_opt
-- name    : MinSumClust_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:22.61136+00:00
-- url     : https://prove2.me/theorems/9fe6e83a-c64c-442c-afc5-c08a549703bd
-- title:
--   Feasible $k$-clusterings, their cost, and the optimum $\mathrm{opt}$
-- statement:
--   A clustering of the $n$ clients of an instance is given by a **labelling** $L=(L_0,\dots,L_{n-1})$ of natural numbers: the clusters are the nonempty label classes, and the number of clusters $|\mathcal S|$ is the number of distinct labels. The labelling is a **feasible $k$-clustering** if it has length $n$, uses only labels $<k$, and uses every label $c<k$: that is, it is a partition of the clients into exactly $k$ nonempty clusters (p.1, p.42, Claim 59). Its cost is
--
--   $$\mathrm{cost}(L)=\sum_{i,j:\ L_i=L_j} d(i,j),$$
--
--   the sum over ordered pairs of clients in the same cluster, which equals the sum of the cluster costs. The **optimum** is
--
--   $$\mathrm{opt}=\min\Bigl\{\sum_{i,j:\ \sigma(i)=\sigma(j)} d(i,j)\ :\ \sigma:\{0,\dots,n-1\}\to\{0,\dots,k-1\}\ \text{surjective}\Bigr\},$$
--
--   the minimum cost of a partition into exactly $k$ nonempty clusters ($\mathrm{opt}=\mathrm{cost}(\mathrm{OPT})$, p.4).
--
--   **Formalization Note** The minimum is a `Finset.inf'` over the surjections, which exist when $1\le k\le n$; the fallback value $0$ occurs only on malformed instances ($k=0$ or $k>n$).
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §1, p.1 (PDF p.3); §2, p.4 (PDF p.6); Claim 59, p.57

import Mathlib
import Definitions.Def_MinSumClust_Inst

namespace MinSumClust

/-- The label of client `i` in a labelling `L` (entry `i` of the list; `0` past its end). -/
def labelOf (L : List ℕ) (i : ℕ) : ℕ := L.getD i 0

/-- **Number of clusters** `|𝒮|` of a labelling: the number of distinct labels used, i.e. the
number of nonempty label classes.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 2, p.4 (the term `f|S|`). -/
def numClusters (L : List ℕ) : ℕ := L.toFinset.card

/-- **Feasible k-clustering**, §1, p.1 and Claim 59, p.57: a labelling of the `n` clients with
labels `< k` in which every label `c < k` occurs, i.e. a partition of the clients into exactly `k`
nonempty clusters (the label classes). -/
def IsKClustering (I : Inst) (L : List ℕ) : Prop :=
  L.length = I.n ∧ (∀ c ∈ L, c < I.k) ∧ ∀ c < I.k, c ∈ L

/-- **Cost of a labelling** `∑_{S ∈ 𝒮} cost(S)`, §1, p.1: the sum of `d(i, j)` over ordered pairs
of clients with the same label; this equals the sum of the costs of the label classes. -/
noncomputable def labelCost (I : Inst) (L : List ℕ) : ℝ :=
  ∑ i : Fin I.n, ∑ j : Fin I.n, if labelOf L i.val = labelOf L j.val then I.dR i j else 0

/-- The cost of an assignment `σ : Fin n → Fin k` (ordered pairs in the same class). -/
noncomputable def partCost (I : Inst) (σ : Fin I.n → Fin I.k) : ℝ :=
  ∑ i : Fin I.n, ∑ j : Fin I.n, if σ i = σ j then I.dR i j else 0

/-- **Optimal cost** `opt = cost(OPT)`, §2, p.4: the minimum of the cost over all partitions of
the clients into exactly `k` nonempty clusters, i.e. over all surjective `σ : Fin n → Fin k`.

**Formalization Note.** The minimum is a `Finset.inf'` over the surjections; there is one when
`1 ≤ k ≤ n`, so on well-formed instances the value is the true minimum. The fallback value `0`
arises only on malformed instances (`k = 0` or `k > n`). -/
noncomputable def opt (I : Inst) : ℝ :=
  open Classical in
  if h : (Finset.univ.filter fun σ : Fin I.n → Fin I.k => Function.Surjective σ).Nonempty then
    (Finset.univ.filter fun σ : Fin I.n → Fin I.k => Function.Surjective σ).inf' h (partCost I)
  else 0

end MinSumClust


