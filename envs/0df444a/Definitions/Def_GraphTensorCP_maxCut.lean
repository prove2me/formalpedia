-- Prove2me | Definitions.Def_GraphTensorCP_maxCut
-- name    : GraphTensorCP_maxCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:09.044489+00:00
-- url     : https://prove2.me/theorems/06926ac4-8c96-41a0-b725-8e4a772a01f9
-- title:
--   Weighted cuts $\mathrm{cut}_W(S)$, the maximum cut $\mathrm{MaxCut}(W)$, and the support graph
-- statement:
--   Let $W$ be a symmetric nonnegative real $n\times n$ matrix with zero diagonal, $n\ge2$. For a nonempty proper subset $S\subsetneq\{1,\dots,n\}$ the **cut weight** is
--
--   $$\mathrm{cut}_W(S)=\sum_{\substack{1\le i<j\le n\\ |\{i,j\}\cap S|=1}}W_{i,j},$$
--
--   and the **maximum-cut weight** is
--
--   $$\mathrm{MaxCut}(W)=\max_{\emptyset\ne S\subsetneq\{1,\dots,n\}}\mathrm{cut}_W(S).$$
--
--   For a graph $G$, $\mathrm{MaxCut}(G)=\mathrm{MaxCut}(A_G)$ is the largest number of edges crossing a cut. The **support graph** of $W$ has an edge $\{i,j\}$ ($i<j$) exactly when $W_{i,j}>0$.
--
--   The maximum cut gives the lower bound in the mission's goal: flattening a weighted graph tensor across a cut has rank $2^{\mathrm{cut}_W(S)}$.
--
--   **Formalization Note** $\mathrm{MaxCut}$ is a supremum over the finite index type of nonempty proper subsets of `Fin n`; for $n\ge2$ this type is nonempty and the supremum is the maximum. The support graph is `SimpleGraph.fromRel (0 < W i j)`, which for symmetric $W$ has exactly the paper's edges.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.26, p.25 (support graph); Definition 2.27, pp.25–26

import Mathlib

namespace GraphTensorCP

/-- **Weighted cut** `cut_W(S)` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely
Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.27, p.25):
"cut_W(S) = Σ_{1≤i<j≤n, |{i,j}∩S|=1} W_{i,j}".

**Formalization Note.** Vertices are `Fin n`; `|{i,j} ∩ S| = 1` is `i ∈ S ↔ j ∉ S`. The sum is
over unordered pairs `i < j`. -/
def cutWeight {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i, ∑ j, if i < j ∧ (i ∈ S ↔ j ∉ S) then W i j else 0

/-- **Maximum-cut weight** (Zhou, arXiv:2610.34273 (version of 2026-11-03), Definition 2.27,
p.26): "MaxCut(W) = max_{∅≠S⊊{1,...,n}} cut_W(S)".

**Formalization Note.** A supremum over the finite index type of nonempty proper subsets of
`Fin n`. For `n ≥ 2` (the paper's standing assumption) this type is finite and nonempty, so
the supremum is the paper's maximum. For a graph `G`, `MaxCut(G) = maxCut (G.adjMatrix ℝ)`. -/
noncomputable def maxCut {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ S : {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ}, cutWeight W S.1

/-- The **support graph** of a weight matrix (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 2.26, p.25): "its support graph has vertex set {1, . . . , n} and edges (i, j) with
1 ≤ i < j ≤ n and W_{i,j} > 0".

**Formalization Note.** `SimpleGraph.fromRel` symmetrizes: `i ~ j` iff `i ≠ j` and
`W_{i,j} > 0` or `W_{j,i} > 0`; for a symmetric `W` this is the paper's edge set. -/
def supportGraph {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => 0 < W i j)

end GraphTensorCP


