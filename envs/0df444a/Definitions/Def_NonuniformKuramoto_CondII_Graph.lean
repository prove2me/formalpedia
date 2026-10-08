-- Prove2me | Definitions.Def_NonuniformKuramoto_CondII_Graph
-- name    : NonuniformKuramoto_CondII_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:07.637413+00:00
-- url     : https://prove2.me/theorems/415868bf-8df5-407f-921d-f047caa41452
-- title:
--   Incidence matrix H of the complete graph, ‖Hx‖₂, weighted Laplacian L(a_ij) and algebraic connectivity λ₂
-- statement:
--   Graph-theoretic objects used throughout §V.B of Dörfler and Bullo.
--
--   Fix $n$ nodes $\{1,\dots,n\}$ and write $\mathcal P_n=\{(i,j): i<j\}$ for the edges of the complete graph, each taken once.
--
--   1. The **incidence matrix of the complete graph** is $H\in\mathbb R^{n(n-1)/2\times n}$ whose row for the edge $(i,j)\in\mathcal P_n$ has $+1$ in column $j$, $-1$ in column $i$ and zeros elsewhere, so that $Hx=(x_2-x_1,\dots)$ is the vector of all pairwise differences of $x\in\mathbb R^n$ and
--   $$
--   \|Hx\|_2=\Big(\sum_{i<j}(x_j-x_i)^2\Big)^{1/2}.
--   $$
--   2. $\|v\|_2=(\sum_i v_i^2)^{1/2}$ is the Euclidean norm, and $\mathbf{sin}(v)=(\sin v_1,\dots,\sin v_m)$ the multivariable sine.
--   3. For a matrix $A=(a_{ij})\in\mathbb R^{n\times n}$, the **Laplacian** is $L(a_{ij})=\operatorname{diag}\big(\sum_{j=1}^n a_{ij}\big)-A$. When $A=A^T$ it is a real symmetric matrix, and for $n\ge 2$ its **algebraic connectivity** $\lambda_2(L(a_{ij}))$ is its second-smallest eigenvalue, counted with multiplicity.
--   4. The graph induced by a nonnegative matrix $A$ has an edge between $i$ and $j$ when $a_{ij}>0$; its undirected edges are the pairs $(i,j)$ with $i<j$ and $a_{ij}>0$, and its **incidence matrix** $B$ has, in the row of the edge $(i,j)$, $+1$ in column $j$ and $-1$ in column $i$. The graph is **connected** when every node is reachable from every other node along edges.
--
--   These objects carry the Lyapunov analysis of the non-uniform Kuramoto model: $\|H\theta\|_2$ measures phase cohesiveness and $\lambda_2$ of the lossless coupling measures the network's connectivity.
--
--   **Formalization Note** Mathlib's `eigenvalues₀` lists the eigenvalues of a Hermitian matrix in decreasing order, so $\lambda_2$ is the entry of index $n-2$. Off its domain ($A$ not symmetric, or $n<2$) `lambda2` returns $0$ by convention; every statement using it assumes both $A=A^T$ and $n\ge2$. The page writes $\|H\theta\|_2=(\sum_i\sum_j|\theta_i-\theta_j|^2)^{1/2}$ (p. 23), which counts every pair twice and contradicts $H\in\mathbb R^{n(n-1)/2\times n}$ and (34); the pair sum is used here.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, pp. 4–5, §I Graph theory (Laplacian, incidence matrix, algebraic connectivity); p. 23, H and ‖Hθ‖₂; p. 5, sin and sinc

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondII

open Matrix

/-- The ordered pairs `(i, j)` with `i < j`: the edges of the complete graph on `n` nodes, each
taken once. They index the rows of the incidence matrix `H` (Dörfler–Bullo, p. 4 and p. 23). -/
abbrev Pairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The incidence matrix `H ∈ ℝ^{n(n−1)/2 × n}` of the complete graph: the row of the edge
`(i, j)`, `i < j`, has `+1` at the sink `j` and `−1` at the source `i`, so that
`(H x)_{(i,j)} = x_j − x_i` and `H x = (x₂ − x₁, …)` (pp. 4–5, p. 23). -/
def incH (n : ℕ) : Matrix (Pairs n) (Fin n) ℝ :=
  fun p k => if k = p.1.2 then 1 else if k = p.1.1 then -1 else 0

/-- The Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` of a finite real vector. -/
noncomputable def euclNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- `‖H x‖₂ = (∑_{i<j} (x_j − x_i)²)^{1/2}`, the two-norm of the vector of all pairwise
differences of `x ∈ ℝⁿ`. -/
noncomputable def normH {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  euclNorm (incH n *ᵥ x)

/-- The multivariable sine `sin(x) = (sin x₁, …, sin x_m)` (p. 5). -/
noncomputable def sinv {ι : Type*} (x : ι → ℝ) : ι → ℝ :=
  fun i => Real.sin (x i)

/-- For a symmetric weight matrix the Laplacian is a symmetric (Hermitian) real matrix. -/
theorem lap_isHermitian {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    (NonuniformKuramoto.CondI.lap A).IsHermitian := by
  unfold NonuniformKuramoto.CondI.lap
  refine Matrix.IsHermitian.sub (Matrix.isHermitian_diagonal_of_self_adjoint _ ?_) ?_
  · ext i; simp
  · ext i j; simp [Matrix.conjTranspose_apply, hA j i]

/-- The algebraic connectivity `λ₂(L(a_ij))`: the second-smallest eigenvalue, counted with
multiplicity, of the Laplacian of a symmetric weight matrix `A` with `n ≥ 2` nodes (p. 5).
Mathlib's `eigenvalues₀` lists the eigenvalues in decreasing order, so the second-smallest one
has index `n − 2`. Off its domain (`A` not symmetric, or `n < 2`) the value is `0` by convention;
every statement using `lambda2` assumes both. -/
noncomputable def lambda2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  if h : (∀ i j, A i j = A j i) ∧ 2 ≤ n then
    (lap_isHermitian A h.1).eigenvalues₀ ⟨Fintype.card (Fin n) - 2, by simp; omega⟩
  else 0

/-- The undirected edges of the graph induced by a nonnegative symmetric matrix `A`: the pairs
`(i, j)` with `i < j` and `a_ij > 0` (p. 4). -/
def IsEdge {n : ℕ} (A : Fin n → Fin n → ℝ) (p : Fin n × Fin n) : Prop :=
  p.1 < p.2 ∧ 0 < A p.1 p.2

/-- The edge set of the graph induced by `A`, as a type. -/
abbrev Edges {n : ℕ} (A : Fin n → Fin n → ℝ) := {p : Fin n × Fin n // IsEdge A p}

noncomputable instance {n : ℕ} (A : Fin n → Fin n → ℝ) : Fintype (Edges A) := by
  classical exact Subtype.fintype _

/-- The incidence matrix `B ∈ ℝ^{|E| × n}` of the graph induced by `A`: the row of the edge
`(i, j)`, `i < j`, has `+1` at `j` and `−1` at `i` (p. 4). -/
def incB {n : ℕ} (A : Fin n → Fin n → ℝ) : Matrix (Edges A) (Fin n) ℝ :=
  fun e k => if k = e.1.2 then 1 else if k = e.1.1 then -1 else 0

/-- The graph induced by `A` (an edge `a → b` whenever `a_ab > 0`) is connected: every node is
reachable from every other node along edges. -/
def IsConnectedGraph {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < A a b) i j

end NonuniformKuramoto.CondII


