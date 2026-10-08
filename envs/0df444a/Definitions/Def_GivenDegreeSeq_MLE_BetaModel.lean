-- Prove2me | Definitions.Def_GivenDegreeSeq_MLE_BetaModel
-- name    : GivenDegreeSeq_MLE_BetaModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:19.067512+00:00
-- url     : https://prove2.me/theorems/6ad9a5ba-296d-469b-8419-d47daffbbede
-- title:
--   The $\beta$-model law $\mathbb P_\beta$ on simple graphs, degree sequences, and the sets $\mathcal D$ and $\mathcal R$
-- statement:
--   Let $n\ge 0$ and $\beta\in\mathbb R^n$. A graph on the vertex set $\{1,\dots,n\}$ is an undirected simple graph (no loops, no multiple edges); the degree sequence $d_1,\dots,d_n$ of a graph $G$ lists the number of neighbours of each vertex.
--
--   1. The **$\beta$-model** $\mathbb P_\beta$ is the law of the random graph in which, for each pair $i\ne j$, the edge $\{i,j\}$ is present with probability $p_{ij}=e^{\beta_i+\beta_j}/(1+e^{\beta_i+\beta_j})$, independently of all other edges. Concretely, $\mathbb P_\beta$ gives each graph $G$ the mass
--   $$w_\beta(G)=\prod_{i<j}\begin{cases}p_{ij}, & \{i,j\}\in E(G),\\ 1-p_{ij}, & \{i,j\}\notin E(G).\end{cases}$$
--   2. $\mathcal D$ is the set of all degree sequences of simple graphs on $n$ vertices, viewed as vectors in $\mathbb R^n$.
--   3. $\mathcal R$ is the set of all **expected degree sequences** $\big(\mathbb E_\beta d_1,\dots,\mathbb E_\beta d_n\big)$ of graphs drawn from $\mathbb P_\beta$, as $\beta$ ranges over $\mathbb R^n$.
--
--   Theorem 1.4 of the paper identifies the closure of $\mathcal R$ with the convex hull of $\mathcal D$; Theorem 1.3 is a statement about $\mathbb P_\beta$-probabilities of events defined through the degree sequence.
--
--   **Formalization Note** Graphs are `SimpleGraph (Fin n)`, a finite type, equipped with Mathlib's σ-algebra on simple graphs, which on this finite type is the discrete one (every set of graphs is an event). $\mathbb P_\beta$ is the finite sum $\sum_G w_\beta(G)\,\delta_G$; that this is a probability measure and that $w_\beta(G)=e^{\sum_i\beta_i d_i}/\prod_{i<j}(1+e^{\beta_i+\beta_j})$ is a separate theorem of this mission, not part of the definition. Expected degrees are Bochner integrals of the (bounded) degree functions against this finite measure. The CAPTAIN conventions of the series fix these bodies; mission 2 of the series (namespace `GivenDegreeSeq.MeanPolytope`) is the reference wording.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (the law P_β), p. 8 Theorem 1.4 (the sets D and R)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_Basic

namespace GivenDegreeSeq.MLE

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5: the β-model law `P_β` on simple graphs (p. 6), the degree sequence of a
graph, the set `D` of degree sequences and the set `R` of expected degree sequences
(Theorem 1.4, p. 8).

A graph on the vertex set `Fin n` is a `SimpleGraph (Fin n)` (no loops, no multiple edges). The
σ-algebra on graphs is Mathlib's `SimpleGraph.instMeasurableSpace` (the pull-back along `Adj` of
the product σ-algebra); on the finite type `SimpleGraph (Fin n)` every set is measurable, so it is
the discrete σ-algebra (every set of graphs is an event). -/

open MeasureTheory

open Classical in
/-- The degree sequence of `G`, as a real vector: `deg G i = d_i` is the number of neighbours
of vertex `i`. -/
noncomputable def deg {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  fun i => (G.degree i : ℝ)

open Classical in
/-- The independent-edge weight of `G` under the β-model: the product over unordered pairs
`{i, j}` (written `i < j`) of `p_ij` if `ij` is an edge of `G` and `1 − p_ij` otherwise. -/
noncomputable def graphWeight {n : ℕ} (β : Fin n → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (if G.Adj i j then GivenDegreeSeq.FixedPoint.edgeProb β i j else 1 - GivenDegreeSeq.FixedPoint.edgeProb β i j)

open Classical in
/-- The β-model law `P_β` (p. 6): for each pair `i ≠ j` an edge is present with probability
`p_ij = e^{β_i+β_j}/(1 + e^{β_i+β_j})`, independently of all other edges. As a measure on the
finite space of simple graphs, `P_β = Σ_G w_β(G) δ_G` with the independent-edge weight `w_β`. -/
noncomputable def betaModel {n : ℕ} (β : Fin n → ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n), ENNReal.ofReal (graphWeight β G) • Measure.dirac G

/-- `D`: the set of all degree sequences of simple graphs on `n` vertices (Theorem 1.4, p. 8). -/
def D (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ∃ G : SimpleGraph (Fin n), y = deg G}

/-- `R`: the set of expected degree sequences `(E_β d_1, …, E_β d_n)` of graphs drawn from `P_β`,
as `β` ranges over `ℝⁿ` (Theorem 1.4, p. 8). -/
noncomputable def R (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun β : Fin n → ℝ => fun i => ∫ G, deg G i ∂ betaModel β)

end GivenDegreeSeq.MLE


