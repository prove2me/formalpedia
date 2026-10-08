-- Prove2me | Definitions.Def_GivenDegreeSeq_MeanPolytope_Model
-- name    : GivenDegreeSeq_MeanPolytope_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:46.178385+00:00
-- url     : https://prove2.me/theorems/07ed5437-4d13-459d-bec9-ddee33db2e11
-- title:
--   The β-model P_β, the degree sequences D, the expected degree sequences R, and the functions g and f_y
-- statement:
--   This file fixes the objects of §1.2 and §3 of Chatterjee, Diaconis and Sly, *Random Graphs with a Given Degree Sequence*.
--
--   **Graphs and degree sequences.** The vertex set is $\{1,\dots,n\}$, and a graph is an undirected simple graph $G$ on it (no loops, no multiple edges). The **degree sequence** of $G$ is the vector $d(G)=(d_1,\dots,d_n)\in\mathbb R^n$, where $d_i$ is the number of neighbours of vertex $i$. The set of all degree sequences is
--   $$\mathcal D=\{d(G):\ G \text{ a simple graph on } n \text{ vertices}\}\subseteq\mathbb R^n.$$
--
--   **The β-model.** For $\beta=(\beta_1,\dots,\beta_n)\in\mathbb R^n$ and $i\neq j$ let
--   $$p_{ij}=\frac{e^{\beta_i+\beta_j}}{1+e^{\beta_i+\beta_j}}.$$
--   The law $\mathbb P_\beta$ is the law of the random graph in which each pair $\{i,j\}$ is an edge with probability $p_{ij}$, independently of all other pairs:
--   $$\mathbb P_\beta(\{G\})=\prod_{i<j}\big(p_{ij}\,\mathbf 1[ij\in G]+(1-p_{ij})\,\mathbf 1[ij\notin G]\big).$$
--
--   **Expected degree sequences.** The set
--   $$\mathcal R=\big\{\big(\mathbb E_\beta[d_1],\dots,\mathbb E_\beta[d_n]\big):\ \beta\in\mathbb R^n\big\}$$
--   collects the expected degree sequences of the β-model as $\beta$ ranges over $\mathbb R^n$.
--
--   **The functions of §3.** For $x\in\mathbb R^n$ let
--   $$g_i(x)=\sum_{j\neq i}\frac{e^{x_i+x_j}}{1+e^{x_i+x_j}},\qquad i=1,\dots,n,$$
--   and for $y\in\mathbb R^n$ let
--   $$f_y(x)=\sum_{i=1}^n x_iy_i-\log\prod_{1\le i<j\le n}\big(1+e^{x_i+x_j}\big)=\sum_{i=1}^n x_iy_i-\sum_{1\le i<j\le n}\log\big(1+e^{x_i+x_j}\big).$$
--
--   These are the objects of Theorem 1.4, which identifies the closure of $\mathcal R$ with the convex hull of $\mathcal D$, and of its proof.
--
--   **Formalization Note** Vertices are `Fin n`, so the paper's vertex $i$ is the Lean index $i-1$. Graphs are `SimpleGraph (Fin n)`, which has finitely many elements. The σ-algebra on graphs is Mathlib's `SimpleGraph.instMeasurableSpace`, which on this finite type makes every set measurable. $\mathbb P_\beta$ is defined in its independent-edge form, as a finite sum of weighted Dirac masses; that it is a probability measure and equals the exponential-family formula of p. 6 are theorems of the mission, not part of the definition. $\mathcal R$ is defined through expectations (Bochner integrals) under $\mathbb P_\beta$, not as the range of $g$; their equality is a theorem. In $f_y$ the paper prints $\log\sum_{i<j}(1+e^{x_i+x_j})$; the product, as written here, is the reading under which the proof of Theorem 1.4 is correct.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (the law P_β), p. 8 (Theorem 1.4: R and D), p. 15 (g and f_y, proof of Theorem 1.4)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.MeanPolytope

open MeasureTheory

/-!
# Chatterjee–Diaconis–Sly (2011), §1.2 and §3: the β-model, the degree sequences `D`, the
expected degree sequences `R`, and the functions `g`, `f_y`

Source: S. Chatterjee, P. Diaconis, A. Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, p. 6 (the law `P_β`), p. 8 (Theorem 1.4: `R`, `D`), p. 15 (`g`, `f_y`).

Conventions.
* The `n` vertices are `Fin n` (the paper's vertex `i ∈ {1, …, n}` is `i - 1 : Fin n`); a graph is
  `G : SimpleGraph (Fin n)` (undirected, no loops, no multiple edges).
* The σ-algebra on graphs is Mathlib's `SimpleGraph.instMeasurableSpace` (the pull-back along
  `Adj` of the discrete σ-algebra on `Fin n → Fin n → Prop`); on the finite type
  `SimpleGraph (Fin n)` every set is measurable, so it is the discrete σ-algebra.
* `P_β` is defined in its independent-edge form: the weight of `G` is the product, over the
  unordered pairs `{i, j}` (written `i < j`), of `p_ij` if `ij` is an edge of `G` and `1 - p_ij`
  otherwise. That this is a probability measure and equals the exponential-family formula of p. 6
  are theorems, not part of the definition.
* `R` is defined through expectations under `P_β`, not as the range of `g`.
* `f_y` uses `Σ_{i<j} log(1 + e^{x_i+x_j}) = log ∏_{i<j}(1 + e^{x_i+x_j})`; the printed
  `log Σ_{i<j}(…)` on p. 15 is a typo (see the mission's notes).
-/

open Classical in
/-- The degree sequence of `G`, as a real vector: `degSeq G i = deg_G(i)`. -/
noncomputable def degSeq {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  fun i => (G.degree i : ℝ)

open Classical in
/-- The probability of the graph `G` when each pair `{i, j}`, `i < j`, is an edge independently
with probability `p_ij`. -/
noncomputable def graphWeight {n : ℕ} (β : Fin n → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (if G.Adj i j then GivenDegreeSeq.FixedPoint.edgeProb β i j else 1 - GivenDegreeSeq.FixedPoint.edgeProb β i j)

open Classical in
/-- The law `P_β` of the β-model on graphs with vertex set `Fin n` (p. 6). -/
noncomputable def betaModel {n : ℕ} (β : Fin n → ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n), ENNReal.ofReal (graphWeight β G) • Measure.dirac G

/-- `D`: the set of all degree sequences of (simple, undirected) graphs on `n` vertices (p. 8). -/
def D (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ∃ G : SimpleGraph (Fin n), y = degSeq G}

/-- `R`: the set of all expected degree sequences `(E_β[deg 1], …, E_β[deg n])` of the β-model,
as `β` ranges over `ℝⁿ` (p. 8). -/
noncomputable def R (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun β : Fin n → ℝ => fun i => ∫ G, degSeq G i ∂ betaModel β)

/-- `g_i(x) = Σ_{j≠i} e^{x_i+x_j} / (1 + e^{x_i+x_j})` (p. 15). -/
noncomputable def g {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.univ.erase i, Real.exp (x i + x j) / (1 + Real.exp (x i + x j))

/-- `f_y(x) = Σ_i x_i y_i − log ∏_{i<j} (1 + e^{x_i+x_j})` (p. 15, with the product of the
p. 16 formula in place of the printed sum). -/
noncomputable def fy {n : ℕ} (y x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i -
    ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), Real.log (1 + Real.exp (x i + x j))

end GivenDegreeSeq.MeanPolytope


