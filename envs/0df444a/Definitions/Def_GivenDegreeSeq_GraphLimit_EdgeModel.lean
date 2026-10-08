-- Prove2me | Definitions.Def_GivenDegreeSeq_GraphLimit_EdgeModel
-- name    : GivenDegreeSeq_GraphLimit_EdgeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:19.383977+00:00
-- url     : https://prove2.me/theorems/e309033e-82be-492a-bef4-09a96c266485
-- title:
--   Random graphs with independent edges, the β-model $P_\beta$, and graphs with a given degree sequence
-- statement:
--   Let $n\ge0$ and let $(p_{ij})$ be real numbers indexed by pairs of vertices of $\{1,\dots,n\}$.
--
--   1. The **random graph with independent edges** of probabilities $p_{ij}$ is the law on simple graphs on $\{1,\dots,n\}$ that gives the graph $G$ the probability
--   $$\prod_{1\le i<j\le n}\begin{cases}p_{ij}&\text{if }\{i,j\}\text{ is an edge of }G,\\ 1-p_{ij}&\text{otherwise.}\end{cases}$$
--   It is a probability measure whenever $0\le p_{ij}\le1$; each pair $\{i,j\}$ is an edge with probability $p_{ij}$ independently of the others.
--   2. For $\beta\in\mathbb R^n$, the **β-model** $P_\beta$ is the random graph with independent edges of probabilities
--   $$p_{ij}=\frac{e^{\beta_i+\beta_j}}{1+e^{\beta_i+\beta_j}}.$$
--   3. For a sequence $d=(d_1,\dots,d_n)$, the set of graphs **with degree sequence $d$** is $\{G:\deg_G(i)=d_i\text{ for all }i\}$.
--
--   Lemmas 6.1 and 6.2 concern general random graphs with independent edges; the β-model is the bridge from independent-edge graphs to uniformly random graphs with a given degree sequence in the proof of Theorem 1.1.
--
--   **Formalization Note** The law is the finite sum $\sum_G w_p(G)\,\delta_G$ of Dirac masses on `SimpleGraph (Fin n)` with Mathlib's σ-algebra (which is discrete on this finite type). Only the entries $p_{ij}$ with $i<j$ enter; theorems that use $d_i=\sum_{j\ne i}p_{ij}$ assume $p$ symmetric. That this is a probability measure is a theorem, not part of the definition. The β-model body agrees with `betaModel` of missions 2 and 3 of this series.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (§1.2, the β-model), p. 26 (Lemmas 6.1–6.2, random graphs with independent edges) and p. 4 (graphs with degree sequence dⁿ)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.GraphLimit

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5: random graphs on `n` vertices with independent edges (p. 26: Lemmas 6.1 and
6.2), the β-model `P_β` (p. 6), and the set of graphs with a given degree sequence (p. 4).

A graph on the vertex set `Fin n` is a `SimpleGraph (Fin n)`. The σ-algebra on graphs is
Mathlib's `SimpleGraph` measurable space; on the finite type `SimpleGraph (Fin n)` every set is
measurable (the discrete σ-algebra). -/

open MeasureTheory

open Classical in
/-- The independent-edge weight of `G` for edge probabilities `p`: the product over unordered
pairs `{i, j}` (written `i < j`) of `p_ij` if `ij` is an edge of `G` and `1 − p_ij` otherwise. -/
noncomputable def graphWeight {n : ℕ} (p : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (if G.Adj i j then p i j else 1 - p i j)

open Classical in
/-- The law of the random graph on `n` vertices in which each pair `{i, j}`, `i < j`, is an edge
with probability `p_ij`, independently of all other pairs:
`Σ_G w_p(G) δ_G`. It is a probability measure when `0 ≤ p_ij ≤ 1` for `i < j` (a theorem, not
part of the definition); only the entries `p_ij` with `i < j` are used. -/
noncomputable def edgeModel {n : ℕ} (p : Fin n → Fin n → ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n), ENNReal.ofReal (graphWeight p G) • Measure.dirac G

/-- The β-model law `P_β` (p. 6): independent edges with `p_ij = e^{β_i+β_j}/(1 + e^{β_i+β_j})`. -/
noncomputable def betaModel {n : ℕ} (β : Fin n → ℝ) : Measure (SimpleGraph (Fin n)) :=
  edgeModel (GivenDegreeSeq.FixedPoint.edgeProb β)

open Classical in
/-- The set of simple graphs on `Fin n` with degree sequence `d`: vertex `i` has degree `d i`. -/
def withDegrees {n : ℕ} (d : Fin n → ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ i, G.degree i = d i}

end GivenDegreeSeq.GraphLimit


