-- Prove2me | Definitions.Def_Grothendieck_Sdp
-- name    : Grothendieck_Sdp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T04:14:05.23493+00:00
-- url     : https://prove2.me/theorems/3ff89e9b-3c91-4a7e-8ac6-e70f2d635a89
-- title:
--   The rank-constrained graphical Grothendieck problem and the constant $K(r,G)$
-- statement:
--   Throughout, $G=(V,E)$ is a finite graph and $A:V\times V\to\mathbb R$ is a **symmetric matrix** indexed by the vertex set of $G$; symmetry is exactly what makes a sum over the *unordered* edge set well defined.
--
--   For a positive integer $r$, the **graphical Grothendieck problem with rank-$r$ constraint** is
--
--   $$
--   \mathrm{SDP}_r(G,A)=\max\Big\{\sum_{\{u,v\}\in E}A(u,v)\,f(u)\cdot f(v)\;:\;f:V\to S^{r-1}\Big\},
--   $$
--
--   where $S^{r-1}=\{x\in\mathbb R^r:x\cdot x=1\}$ is the $(r-1)$-dimensional unit sphere and $f(u)\cdot f(v)$ is the Euclidean inner product. Replacing the sphere $S^{r-1}$ by the unit sphere $S^\infty$ of the real Hilbert space $\ell^2(\mathbb R)$ of square-summable sequences gives the **problem without rank constraint**
--
--   $$
--   \mathrm{SDP}_\infty(G,A)=\max\Big\{\sum_{\{u,v\}\in E}A(u,v)\,f(u)\cdot f(v)\;:\;f:V\to S^{\infty}\Big\},
--   $$
--
--   which is a semidefinite program and can be solved to any fixed precision in polynomial time, whereas the rank-constrained problem is hard already at rank $1$: for $G=K_{n,n}$ and $A$ the Laplacian of a graph it is MAX CUT.
--
--   The **rank-$r$ Grothendieck constant** of $G$ is the smallest constant $K$ such that
--
--   $$
--   \mathrm{SDP}_\infty(G,A)\le K\cdot\mathrm{SDP}_r(G,A)\qquad\text{for every symmetric matrix }A,
--   $$
--
--   and is denoted $K(r,G)$; it satisfies $K(r,G)\ge1$. Proving upper bounds for $K(r,G)$ is the subject of the paper: its main theorem states $K(r,G)\le\beta(r,G)^{-1}$, and Table 1 of the paper evaluates this bound for $r\le10$ on bipartite and tripartite graphs.
--
--   **Formalization Note** The symmetric matrix $A$ is a function `A : V → V → ℝ` together with the hypothesis `∀ u v, A u v = A v u`; the edge sum runs over `G.edgeFinset`, a finite set of unordered pairs, so no orientation of the edges is chosen. $\mathrm{SDP}_r$ and $\mathrm{SDP}_\infty$ are `sSup` of the objective over the feasible sphere, and $K(r,G)$ is the `sInf` of the constants satisfying the inequality for *all* symmetric $A$ (not a supremum of a ratio, which would need a nonvanishing denominator). The sphere $S^{r-1}$ is `EuclideanSpace ℝ (Fin r)` with the condition `‖f v‖ = 1`, and $S^\infty$ is the unit sphere of `lp (fun _ : ℕ => ℝ) 2`.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, p. 78 (definition of SDP_r and SDP_inf) and inequality (1.1), p. 78. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib

/-!
# The graphical Grothendieck problem with rank constraint

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

This file formalizes the optimization layer of the paper:

* `edgeSum G A hA f = ∑_{uv ∈ E} A(u,v) f(u)·f(v)`, the objective (p. 78);
* `sdpRank r G A hA = SDP_r(G,A) = max { ∑_{uv∈E} A(u,v) f(u)·f(v) : f : V → S^{r-1} }` (p. 78);
* `sdpInf G A hA = SDP_∞(G,A)`, the same with `f` ranging over the unit sphere of
  `ℓ²(ℝ)` = `L2` (p. 78);
* `grothendieckConstant r G = K(r,G)`, the smallest constant with
  `SDP_∞(G,A) ≤ K(r,G) · SDP_r(G,A)` for every symmetric `A` (inequality (1.1), p. 78).

The matrix `A` is symmetric, as in the paper; it is encoded as `A : V → V → ℝ`
together with the hypothesis `hA : ∀ u v, A u v = A v u`, which is what makes the
sum over the *unordered* edge set well defined.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The objective `∑_{{u,v} ∈ E} A(u,v) f(u)·f(v)` of the graphical Grothendieck
problem (p. 78), summed over the edge set of `G` and evaluated on a symmetric
matrix `A`. -/
def edgeSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → E) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => A u v * inner ℝ (f u) (f v), by
      intro u v
      simp only [hA u v, real_inner_comm]⟩ e

/-- `SDP_r(G,A)`, the graphical Grothendieck problem with rank-`r` constraint (p. 78):
the maximum of `∑_{uv ∈ E} A(u,v) f(u)·f(v)` over all `f : V → S^{r-1}`. -/
def sdpRank (r : ℕ) (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) : ℝ :=
  sSup {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r),
    (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f}

/-- `ℓ²(ℝ)`, the real Hilbert space of square-summable sequences, in which the unit
sphere `S^∞` of the paper lives. -/
abbrev L2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- `SDP_∞(G,A)` (p. 78): the rank constraint is dropped and `f` ranges over the unit
sphere `S^∞` of `ℓ²(ℝ)`. -/
def sdpInf (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) : ℝ :=
  sSup {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f}

/-- The rank-`r` Grothendieck constant `K(r,G)` of the graph `G` (p. 78): the smallest
constant `K` such that `SDP_∞(G,A) ≤ K · SDP_r(G,A)` holds for every symmetric
matrix `A : V × V → ℝ`, i.e. inequality (1.1). -/
def grothendieckConstant (r : ℕ) (G : SimpleGraph V) : ℝ :=
  sInf {K : ℝ | ∀ (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u),
    sdpInf G A hA ≤ K * sdpRank r G A hA}

end Grothendieck


