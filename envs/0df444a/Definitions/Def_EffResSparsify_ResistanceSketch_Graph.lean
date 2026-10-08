-- Prove2me | Definitions.Def_EffResSparsify_ResistanceSketch_Graph
-- name    : EffResSparsify_ResistanceSketch_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:14.974412+00:00
-- url     : https://prove2.me/theorems/3d8f90e0-a992-4910-9fd0-c43f692b6f96
-- title:
--   Weighted graphs, incidence matrix, Laplacian, pseudoinverse, effective resistance and the L-norm (§2, §4)
-- statement:
--   Let $G=(V,E,w)$ be a weighted undirected graph with finite vertex set $V$, $n=|V|$, finite edge set $E$, $m=|E|$, and edge weights $w_e>0$. Orient every edge arbitrarily: each edge $e$ has a head and a tail, which are distinct vertices. This module fixes the following objects.
--
--   1. The **underlying simple graph** joins $a$ and $b$ when some edge has endpoints $a$ and $b$. $G$ is **connected** when this graph is connected (in particular $V\neq\emptyset$). $G$ is **simple** when no two distinct edges join the same unordered pair of vertices.
--   2. The **signed edge–vertex incidence matrix** $B\in\mathbb R^{E\times V}$:
--   $$
--   B(e,v)=\begin{cases}1 & v \text{ is the head of } e,\\ -1 & v \text{ is the tail of } e,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   3. The diagonal **weight matrix** $W\in\mathbb R^{E\times E}$ with $W(e,e)=w_e$, and the **Laplacian** $L=B^{\mathsf T}WB\in\mathbb R^{V\times V}$.
--   4. The **Moore–Penrose pseudoinverse** $L^+$ of $L$. Since $L$ is symmetric, $L=\sum_{\lambda_i\neq0}\lambda_i u_iu_i^{\mathsf T}$ for orthonormal eigenvectors $u_i$, and $L^+=\sum_{\lambda_i\ne0}\lambda_i^{-1}u_iu_i^{\mathsf T}$.
--   5. For a vertex $u$, the indicator vector $\chi_u\in\mathbb R^V$, and the **effective resistance** between vertices $u$ and $v$:
--   $$
--   R_{uv}=(\chi_u-\chi_v)^{\mathsf T}L^+(\chi_u-\chi_v).
--   $$
--   The effective resistance of an edge $e$ with tail $a$ and head $b$ is $R_e=R_{ab}$.
--   6. The **$L$-norm** of $y\in\mathbb R^V$: $\|y\|_L=\sqrt{y^{\mathsf T}Ly}$.
--   7. The squared Euclidean norm $\|y\|^2=\sum_i y_i^2$ of a vector $y\in\mathbb R^k$.
--
--   These are the objects of the preliminaries of the paper and of its Section 4, in which effective resistances are approximated by a low-dimensional sketch $Z(\chi_u-\chi_v)$.
--
--   **Formalization Note** The graph is a structure `WGraph V E` with `head`, `tail`, `w`, the fields `head e ≠ tail e` and `0 < w e`; connectivity and simplicity are separate predicates, because some statements need only connectivity. $L^+$ is the published pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map $x\mapsto Lx$ on the Euclidean space $\mathbb R^V$ (standard inner product), turned back into a matrix with `Matrix.toEuclideanLin`; for a symmetric matrix this coincides with the spectral formula above. The squared Euclidean norm is written as a sum of squares, so it does not depend on Lean's sup norm on `Fin k → ℝ`.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, pp. 4–6, §2.1 (incidence matrix, W, L = BᵀWB), §2.2 (pseudoinverse), §2.3 (effective resistance of an edge); p. 10, §4 (R_uv = (χ_u − χ_v)ᵀL⁺(χ_u − χ_v), ‖y‖_L in Theorem 8)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

namespace EffResSparsify.ResistanceSketch

open Matrix

/-- A weighted undirected graph `G = (V, E, w)` whose edges carry an arbitrary orientation
(§2.1, p. 4): every edge `e` has a head `head e` and a tail `tail e`, distinct (no loops), and a
weight `w e > 0`. Parallel edges are allowed by the structure; `IsSimple` excludes them. -/
structure WGraph (V E : Type*) where
  /-- the head of the oriented edge `e` -/
  head : E → V
  /-- the tail of the oriented edge `e` -/
  tail : E → V
  /-- the edge weight `w_e` -/
  w : E → ℝ
  head_ne_tail : ∀ e, head e ≠ tail e
  w_pos : ∀ e, 0 < w e

namespace WGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The underlying simple graph on `V`: `a ~ b` iff some edge joins `a` and `b`. -/
def toSimpleGraph (G : WGraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => ∃ e, G.head e = a ∧ G.tail e = b)

/-- `G` is connected (the standing assumption of §2.1, p. 4). Mathlib's `Connected` includes
nonemptiness of `V`. -/
def IsConnected (G : WGraph V E) : Prop := G.toSimpleGraph.Connected

/-- `G` is simple: no two edges join the same unordered pair of vertices. -/
def IsSimple (G : WGraph V E) : Prop :=
  ∀ e e' : E, s(G.head e, G.tail e) = s(G.head e', G.tail e') → e = e'

/-- The signed edge-vertex incidence matrix `B` (§2.1, p. 4): `B(e,v) = 1` if `v` is the head
of `e`, `-1` if `v` is the tail of `e`, and `0` otherwise. -/
def incidence (G : WGraph V E) : Matrix E V ℝ :=
  fun e v => if v = G.head e then 1 else if v = G.tail e then -1 else 0

/-- The diagonal weight matrix `W` with `W(e,e) = w_e` (§2.1, p. 4). -/
def weightMatrix (G : WGraph V E) : Matrix E E ℝ := Matrix.diagonal G.w

/-- The Laplacian `L = Bᵀ W B` (§2.1, p. 4). -/
def laplacian (G : WGraph V E) : Matrix V V ℝ :=
  G.incidenceᵀ * G.weightMatrix * G.incidence

/-- The Moore–Penrose pseudoinverse `L⁺` of the Laplacian (§2.2, p. 5), as a matrix: the
published pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map
`x ↦ L x` on the Euclidean space `ℝ^V`, converted back to a matrix. For the symmetric matrix
`L` this is `∑_{λ_i ≠ 0} λ_i⁻¹ u_i u_iᵀ`. -/
noncomputable def lapPinv (G : WGraph V E) : Matrix V V ℝ :=
  Matrix.toEuclideanLin.symm
    (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin G.laplacian))

/-- The indicator vector `χ_u ∈ ℝ^V` of the vertex `u`. -/
def chi (u : V) : V → ℝ := Pi.single u 1

/-- The effective resistance between vertices `u` and `v` (p. 10):
`R_uv = (χ_u − χ_v)ᵀ L⁺ (χ_u − χ_v)`. The effective resistance of an edge `e` is
`R_e = R (tail e) (head e)` (p. 6). -/
noncomputable def R (G : WGraph V E) (u v : V) : ℝ :=
  (chi u - chi v) ⬝ᵥ (G.lapPinv *ᵥ (chi u - chi v))

/-- The `L`-norm `‖y‖_L = √(yᵀ L y)` of a vector `y ∈ ℝ^V` (Theorem 8, p. 10). -/
noncomputable def lNorm (G : WGraph V E) (y : V → ℝ) : ℝ :=
  Real.sqrt (y ⬝ᵥ (G.laplacian *ᵥ y))

end WGraph

/-- The squared Euclidean norm `‖y‖² = ∑_i y_i²` of a vector `y ∈ ℝ^ι`. -/
def sqNorm {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ i, y i ^ 2

end EffResSparsify.ResistanceSketch


