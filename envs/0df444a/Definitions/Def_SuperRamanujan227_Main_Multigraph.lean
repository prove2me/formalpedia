-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Multigraph
-- name    : SuperRamanujan227_Main_Multigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:23.637684+00:00
-- url     : https://prove2.me/theorems/84f2830d-4877-4a58-a60d-611f283c88c6
-- title:
--   Finite undirected multigraphs with loops counted twice, $d$-regularity and $\lambda_k(G)$
-- statement:
--   A **multigraph** on the vertex set $\{1,\dots,n\}$ may have parallel edges and self-loops. It is recorded by its adjacency matrix $A\in\mathbb N^{n\times n}$: for $u\ne v$, $A_{uv}$ is the number of edges between $u$ and $v$, and $A_{vv}$ is twice the number of self-loops at $v$. Thus $A$ is symmetric with even diagonal entries, and every such matrix is the adjacency matrix of exactly one multigraph.
--
--   The graph is **$d$-regular** if every row sum of $A$ equals $d$; equivalently, every vertex has degree $d$, a self-loop contributing $2$.
--
--   Since $A$ is real symmetric, its eigenvalues are real; for a $d$-regular graph they are written
--   $$d=\lambda_1(G)\ge\lambda_2(G)\ge\cdots\ge\lambda_n(G)\ge-d,$$
--   counted with multiplicity. In particular, if $d$ is a repeated eigenvalue (a disconnected graph), then $\lambda_2(G)=d$.
--
--   This is the graph class of §2 in which Theorem 1.1 is stated; no simplicity or connectedness is assumed.
--
--   **Formalization Note** $\lambda_k(G)$ is $\lambda_k$ of the real adjacency matrix, i.e. the $k$-th largest root of its characteristic polynomial with multiplicity, using the shared definition of $\lambda_k$.
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, §2, pp. 6–7 (graphs with parallel edges and self-loops, loop convention, eigenvalue ordering)

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra

open Polynomial

namespace SuperRamanujan227.Main

/-- A finite undirected multigraph on the vertex set `Fin n`, given by its adjacency matrix
(§2, p. 6): parallel edges and self-loops are allowed; the off-diagonal entry `adj u v` is the
number of edges between `u` and `v`, and the diagonal entry `adj v v` is twice the number of
self-loops at `v`. -/
structure Multigraph (n : ℕ) where
  /-- Adjacency matrix with natural-number entries. -/
  adj : Matrix (Fin n) (Fin n) ℕ
  /-- The graph is undirected. -/
  symm : adj.transpose = adj
  /-- Each self-loop contributes `2` to its diagonal entry. -/
  loops_even : ∀ v, Even (adj v v)

namespace Multigraph

variable {n : ℕ}

/-- `G` is `d`-regular: every row sum of the adjacency matrix (the degree, a self-loop counting
twice) equals `d`. -/
def IsRegular (G : Multigraph n) (d : ℕ) : Prop :=
  ∀ v, ∑ w, G.adj v w = d

/-- The adjacency matrix as a real matrix. -/
noncomputable def adjReal (G : Multigraph n) : Matrix (Fin n) (Fin n) ℝ :=
  G.adj.map (fun k => (k : ℝ))

/-- `λ_k(G)`: the `k`-th largest adjacency eigenvalue, counted with multiplicity
(`d = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ ≥ -d` for a `d`-regular graph, §2, pp. 6–7). -/
noncomputable def eig (G : Multigraph n) (k : ℕ) : ℝ :=
  matrixEig G.adjReal k

end Multigraph

end SuperRamanujan227.Main


