-- Prove2me | Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
-- name    : SpectralSparsify_Sampling_WeightedGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:24.163136+00:00
-- url     : https://prove2.me/theorems/9146d6ca-edc3-461e-aa2b-8e1262583737
-- title:
--   Weighted graphs, the Laplacian quadratic form (1), the Laplacian matrix and σ-spectral approximation (2)
-- statement:
--   Let $V$ be a finite vertex set. A **weighted graph** on $V$ is a function $w : V\times V\to\mathbb R$ with $w(u,v)=w(v,u)$, $w(u,v)\ge 0$ and $w(v,v)=0$; its edges are the pairs with $w(u,v)\neq 0$. An unweighted graph $G$ is the weighted graph with weight $1$ on each edge and $0$ elsewhere.
--
--   The **weighted degree** of $v$ is $d_v=\sum_z w(v,z)$, the **adjacency matrix** is $A(u,v)=w(u,v)$, the **degree matrix** is $D=\operatorname{diag}(d_v)$, and the **Laplacian** is $L=D-A$, i.e. $L(u,v)=-w(u,v)$ for $u\neq v$ and $L(u,u)=\sum_z w(u,z)$. Its quadratic form is
--   $$x^{T}L x=\sum_{\{u,v\}\in E} w(u,v)\,(x(u)-x(v))^2=\frac12\sum_{u\in V}\sum_{v\in V} w(u,v)\,(x(u)-x(v))^2 ,\qquad x\in\mathbb R^V. $$
--
--   A weighted graph $\widetilde G$ is a **$\sigma$-spectral approximation** ($\sigma$-approximation) of $G$ if for every $x\in\mathbb R^V$
--   $$\frac1\sigma\, x^{T}L_{\widetilde G}x\le x^{T}L_G x\le \sigma\, x^{T}L_{\widetilde G}x .$$
--
--   These are the objects the paper's statements are phrased in: (S.1) of Theorem 6.1, the conclusion of Lemma 6.2 and the conclusion of Lemma 10.2 are $\sigma$-approximations. The paper only uses $\sigma\ge 1$.
--
--   **Formalization Note** A weighted graph is a bare function `w : V → V → ℝ`; `IsWGraph w` records symmetry, nonnegativity and the absence of loops, and is assumed where the paper says "graph". `lapForm w x` sums over ordered pairs with the factor $1/2$, so each undirected edge counts once, as in (1). For an unweighted graph it agrees with Mathlib's `SimpleGraph.lapMatrix_toLinearMap₂'`. `IsApprox σ wt w` reads "`wt` is a $\sigma$-approximation of `w`" and keeps both inequalities of (2); it is meant for $\sigma>0$ (at $\sigma=0$ Lean's $1/0=0$ would make it say $x^TL_Gx=0$), and every statement using it has $\sigma\ge1$. `lapMat` equals the paper's $L_G$ for loopless weights, which `IsWGraph` guarantees.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 2, (1) and (2); §4, p. 4, (3)

import Mathlib

namespace SpectralSparsify.Sampling

/-- A weighted graph on the finite vertex set `V`, given by its weight function `w`
(Spielman–Teng, *Spectral Sparsification of Graphs*, arXiv:0808.4134v3, §1, p. 2): `w u v` is the
weight of the edge `{u, v}`, weights are symmetric and nonnegative, and there are no self-loops.
The edges are the pairs with `w u v ≠ 0`. -/
def IsWGraph {V : Type*} (w : V → V → ℝ) : Prop :=
  (∀ u v, w u v = w v u) ∧ (∀ u v, 0 ≤ w u v) ∧ (∀ v, w v v = 0)

/-- The unweighted graph `G` viewed as a weighted graph: weight `1` on each edge, `0` elsewhere. -/
def adjWeight {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  if G.Adj u v then 1 else 0

/-- The Laplacian quadratic form (1), p. 2: `xᵀ L_G x = ∑_{(u,v) ∈ E} w(u,v) (x(u) - x(v))²`.
The double sum over ordered pairs counts each undirected edge twice, hence the factor `1/2`. -/
noncomputable def lapForm {V : Type*} [Fintype V] (w : V → V → ℝ) (x : V → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, w u v * (x u - x v) ^ 2

/-- The weighted degree `d_v = ∑_z w(v, z)`. -/
noncomputable def wDegree {V : Type*} [Fintype V] (w : V → V → ℝ) (v : V) : ℝ :=
  ∑ z, w v z

/-- The weighted adjacency matrix `A(u, v) = w(u, v)`. -/
def adjMat {V : Type*} (w : V → V → ℝ) : Matrix V V ℝ :=
  Matrix.of w

/-- The diagonal matrix of weighted degrees `D = diag(d_v)`. -/
noncomputable def degMat {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) :
    Matrix V V ℝ :=
  Matrix.diagonal (wDegree w)

/-- The Laplacian matrix `L = D - A`, p. 2: `L(u, v) = -w(u, v)` for `u ≠ v` and
`L(u, u) = ∑_z w(u, z)` (for a loopless `w`). -/
noncomputable def lapMat {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) :
    Matrix V V ℝ :=
  degMat w - adjMat w

/-- `σ`-spectral approximation (2), p. 2: `w̃` is a `σ`-approximation of `w` when, for every
`x ∈ ℝ^V`, `(1/σ) xᵀ L_{G̃} x ≤ xᵀ L_G x ≤ σ xᵀ L_{G̃} x`. Argument order as in the sentence
"`G̃` is a `σ`-approximation of `G`": `IsApprox σ w̃ w`. -/
def IsApprox {V : Type*} [Fintype V] (σ : ℝ) (wt w : V → V → ℝ) : Prop :=
  ∀ x : V → ℝ, (1 / σ) * lapForm wt x ≤ lapForm w x ∧ lapForm w x ≤ σ * lapForm wt x

end SpectralSparsify.Sampling


