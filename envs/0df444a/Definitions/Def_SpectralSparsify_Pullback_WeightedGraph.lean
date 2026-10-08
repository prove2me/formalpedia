-- Prove2me | Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
-- name    : SpectralSparsify_Pullback_WeightedGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:45.716283+00:00
-- url     : https://prove2.me/theorems/4d406146-673f-4b01-a8a1-0aa36c4951e9
-- title:
--   The order G ≼ G̃ of Laplacian quadratic forms and the unit edge (u, v), on top of weighted graphs, (1) and (2)
-- statement:
--   Let $V$ be a finite vertex set. A **weighted graph** on $V$ is a function $w : V\times V\to\mathbb R$ with $w(u,v)=w(v,u)$, $w(u,v)\ge 0$ and $w(v,v)=0$; its edges are the pairs with $w(u,v)\neq 0$. The **sum** $G+H$ of two weighted graphs on $V$ adds their weights, and the scalar multiple $cG$ multiplies every weight by $c$.
--
--   The **Laplacian quadratic form** of $G=(V,E,w)$ is
--   $$x^{T}L_G x=\sum_{(u,v)\in E} w(u,v)\,(x(u)-x(v))^2=\frac12\sum_{u\in V}\sum_{v\in V} w(u,v)\,(x(u)-x(v))^2 ,\qquad x\in\mathbb R^V,$$
--   which counts each undirected edge once.
--
--   A weighted graph $\widetilde G$ is a **$\sigma$-spectral approximation** ($\sigma$-approximation) of $G$ if for every $x\in\mathbb R^V$
--   $$\frac1\sigma\, x^{T}L_{\widetilde G}x\le x^{T}L_G x\le \sigma\, x^{T}L_{\widetilde G}x .$$
--   We write $G\preccurlyeq G'$ when $x^{T}L_G x\le x^{T}L_{G'}x$ for every $x$. Finally, $(u,v)$ also denotes the graph consisting of the single edge $\{u,v\}$ of weight $1$.
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** This module defines only `GraphLE` and `unitEdge`; `IsWGraph`, `lapForm` and `IsApprox` are imported from the shared module `SpectralSparsify.Sampling` (`Def_SpectralSparsify_Sampling_WeightedGraph`). A weighted graph is a bare function `w : V → V → ℝ`; `IsWGraph w` records symmetry, nonnegativity and the absence of loops and is assumed where the paper says "weighted graph". Graph sums and scalar multiples are the pointwise `w + w'` and `c • w`. `lapForm w x` sums over ordered pairs with the factor $1/2$; for an unweighted graph it agrees with Mathlib's `SimpleGraph.lapMatrix_toLinearMap₂'`. `IsApprox σ wt w` reads "`wt` is a $\sigma$-approximation of `w`" and keeps both inequalities of (2); `GraphLE w w'` is $G\preccurlyeq G'$. `unitEdge u v` has weight $1$ on $(u,v)$ and $(v,u)$; it is only used with $u\neq v$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 2, (1) and (2); §4, p. 4 (≼, graph sums)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph

namespace SpectralSparsify.Pullback

/-- The order `G ≼ G'` of §4, p. 4: `L_G ≼ L_{G'}`, i.e. `xᵀ L_G x ≤ xᵀ L_{G'} x` for every `x`. -/
def GraphLE {V : Type*} [Fintype V] (w w' : V → V → ℝ) : Prop :=
  ∀ x : V → ℝ, SpectralSparsify.Sampling.lapForm w x ≤ SpectralSparsify.Sampling.lapForm w' x

/-- The graph consisting of the single edge `(u, v)` of weight `1` (for `u ≠ v`). -/
def unitEdge {V : Type*} [DecidableEq V] (u v : V) : V → V → ℝ :=
  fun a b => if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0

end SpectralSparsify.Pullback


