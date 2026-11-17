-- Prove2me | Definitions.Def_HardcoreSlices_Supplement_indepSlice
-- name    : HardcoreSlices_Supplement_indepSlice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:28:22.274749+00:00
-- url     : https://prove2.me/theorems/92de16c7-f943-43de-b266-4460572aa81b
-- title:
--   The independent set slice $(X,\mu^{(k)})$ of a graph
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $k\ge0$ an integer. The **independent set slice** of $G$ at size $k$ consists of three objects.
--
--   1. The facets $\mathcal I_k(G)$: the independent sets $I\subseteq V$ (no edge of $G$ has both endpoints in $I$) with $|I|=k$.
--   2. The complex $X$: the downward closure of $\mathcal I_k(G)$, i.e. all subsets of $V$ contained in some $I\in\mathcal I_k(G)$. Dimension is cardinality, so $X$ is a $k$-dimensional simplicial complex.
--   3. The law $\mu^{(k)}$: the uniform distribution on $\mathcal I_k(G)$,
--   $$\mu^{(k)}(I)=\begin{cases}1/|\mathcal I_k(G)| & I\in\mathcal I_k(G),\\ 0 & \text{otherwise.}\end{cases}$$
--
--   The down-up walk on $(X,\mu^{(k)})$ removes a uniformly random vertex from the current independent set and adds a uniformly random admissible vertex; it is the natural Markov chain for sampling a uniform independent set of a fixed size, and it is the chain of Theorem 1.10.
--
--   **Formalization Note** The graph is an arbitrary simple graph on a finite vertex type, not a bipartite one. The complex is the mission's published `downClosure`; independence is Mathlib's `SimpleGraph.IsIndepSet`. When $\mathcal I_k(G)$ is empty the law is identically $0$; Theorem 1.10 asserts nonemptiness in its range.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), §1.2 "Independent Set Slice", p.4

import Mathlib
import Definitions.Def_HardcoreSlices_downUp

open Classical

namespace HardcoreSlices.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `I_k(G)`, the independent sets of size `k`. Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on
Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…),
§1.2 "Independent Set Slice", p.4: "Given a graph `G = (V, E)`, let `Ik(G)` be the set of independent sets `I ∈ I(G)`
with `|I| = k`".

**Formalization Note.** Independence is Mathlib's `SimpleGraph.IsIndepSet`: no two vertices of `I` are adjacent.
The graph is an arbitrary simple graph on a finite vertex type; it is not assumed bipartite. -/
noncomputable def indepFacets (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun I => G.IsIndepSet (I : Set V) ∧ I.card = k)

/-- The independent set slice complex (§1.2, p.4): "We can also define the `k`-dimensional complex `(X, µ(k))`
analogously", that is, the downward closure of `I_k(G)` over the ground set `V`, as for the two-sided slice
(Definition 1.6, p.3).

**Formalization Note.** Dimension is cardinality (p.1, footnote 1), so the facets have `k` vertices and the
complex is the published `HardcoreSlices.downClosure` of `I_k(G)`. -/
noncomputable def indepComplex (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  HardcoreSlices.downClosure (indepFacets G k)

/-- `µ^{(k)}`, "the uniform distribution over `Ik(G)`" (§1.2, p.4): `1/|I_k(G)|` on each independent set of size
`k`, and `0` on every other set.

**Formalization Note.** When `I_k(G)` is empty this function is identically `0`; the statement using it asserts
that `I_k(G)` is nonempty in its range of `k`. -/
noncomputable def indepLaw (G : SimpleGraph V) (k : ℕ) (I : Finset V) : ℝ :=
  if I ∈ indepFacets G k then 1 / ((indepFacets G k).card : ℝ) else 0

end HardcoreSlices.Supplement


