-- Prove2me | Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
-- name    : ExplicitExpanders_Attach_IsNDLambda
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:34.773143+00:00
-- url     : https://prove2.me/theorems/03198f97-8892-4ac4-a01f-8857423084ef
-- title:
--   $(n, d, \lambda)$-graphs, at the level of adjacency matrices with loops (Section 1)
-- statement:
--   An **$(n, d, \lambda)$-graph** is a $d$-regular graph on $n$ vertices in which the absolute value of every nontrivial eigenvalue is at most $\lambda$. The trivial eigenvalue is the top eigenvalue $d$, whose eigenvector is the constant vector $\mathbf 1$.
--
--   This file states the notion at two levels.
--
--   1. **Matrices.** Let $A$ be a real square matrix indexed by a finite set $V$. Then $A$ is an $(n, d, \lambda)$ matrix when $|V| = n$, $A$ is symmetric, every row of $A$ sums to $d$ (that is, $A\mathbf 1 = d\,\mathbf 1$), and
--   $$\text{for every } \mu\in\mathbb R \text{ and } f\colon V\to\mathbb R,\qquad f\neq 0,\ \ \sum_{v\in V} f(v)=0,\ \ Af=\mu f \ \Longrightarrow\ |\mu|\le\lambda .$$
--   2. **Simple graphs.** A simple graph $G$ on $V$ is an $(n, d, \lambda)$-graph when it is $d$-regular and its real adjacency matrix is an $(n, d, \lambda)$ matrix.
--
--   Since $A$ is symmetric and fixes the line spanned by $\mathbf 1$, it also maps the orthogonal complement $\mathbf 1^{\perp}=\{f : \sum_v f(v)=0\}$ into itself; the eigenvalues of $A$ on $\mathbf 1^\perp$ are exactly all eigenvalues of $A$ except one copy of $d$. So the condition above says that every nontrivial eigenvalue has absolute value at most $\lambda$, which is the paper's definition. The matrix level is needed because the graph constructed in the proof of Theorem 1.2 carries loops, with the paper's convention that a loop adds one to the degree; a loop at $v$ is a diagonal entry $A_{vv}=1$.
--
--   **Formalization Note** The nontrivial eigenvalues are characterised through eigenvectors orthogonal to the constant vector, not by deleting an index of a sorted eigenvalue list. The graph-level predicate also records $d$-regularity explicitly, which for a simple graph is equivalent to the row-sum condition.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 1, Section 1 (definition of an (n, d, λ)-graph); p. 3 (loop convention)

import Mathlib

namespace ExplicitExpanders.Attach

open Matrix

/-- Matrix-level `(n, d, λ)` predicate (Alon, *Explicit expanders of every degree and size*,
arXiv:2003.11673v1, §1, p. 1, with the loop convention of p. 3). The real square matrix `A`,
indexed by a finite type `V`, is an `(n, d, λ)` matrix when `V` has `n` elements, `A` is
symmetric, every row of `A` sums to `d` (equivalently `A` maps the all-ones vector `1` to `d • 1`),
and every eigenvalue `μ` of `A` with an eigenvector `f ≠ 0` orthogonal to `1` (that is,
`∑ v, f v = 0`) satisfies `|μ| ≤ λ`. A loop at a vertex is a diagonal entry `1`. -/
def IsNDLambdaMatrix {V : Type*} [Fintype V] (A : Matrix V V ℝ) (n d : ℕ) (lam : ℝ) : Prop :=
  Fintype.card V = n ∧ A.IsSymm ∧ A *ᵥ 1 = (d : ℝ) • 1 ∧
    ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam

/-- A simple graph `G` on a finite vertex type is an `(n, d, λ)`-graph (§1, p. 1): it is
`d`-regular, and its real adjacency matrix is an `(n, d, λ)` matrix in the sense of
`IsNDLambdaMatrix`. -/
def IsNDLambda {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (lam : ℝ) : Prop :=
  G.IsRegularOfDegree d ∧ IsNDLambdaMatrix (G.adjMatrix ℝ) n d lam

end ExplicitExpanders.Attach


