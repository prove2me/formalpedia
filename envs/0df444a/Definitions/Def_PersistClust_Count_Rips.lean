-- Prove2me | Definitions.Def_PersistClust_Count_Rips
-- name    : PersistClust_Count_Rips
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:59.606523+00:00
-- url     : https://prove2.me/theorems/ddc7a00f-7b57-4abf-b9cd-cde43a2c9e7a
-- title:
--   Definition 2.1, Eqs. (2)–(3) — the Rips graph and the 0-th persistence diagram of the upper-star Rips filtration
-- statement:
--   Let $\iota$ be a finite index set of points with a symmetric distance matrix $D_{ij}$, a function value $g_i$ at each point, and $\delta>0$.
--
--   1. **Rips graph (Definition 2.1).** $R_\delta$ is the graph on $\iota$ with an edge between $i\ne j$ whenever $D_{ij}\le\delta$.
--   2. **Upper-star Rips filtration (Eqs. (2)–(3)).** For $t\in\mathbb R$, $L^t=\{i : g_i\ge t\}$, and $\mathcal R^g_\delta=\{R_\delta(L^t)\}_{t\in\mathbb R}$ is the family of subgraphs of $R_\delta$ induced on $L^t$, with $t$ running from $+\infty$ to $-\infty$.
--   3. **Rank function and diagram.** For $t\le s$, the rank $r(s,t)$ is the number of connected components of $R_\delta(L^t)$ that contain a vertex of $L^s$, and the diagram $D_0\mathcal R^g_\delta$ is obtained from this rank function exactly as for superlevel sets (see the persistence definitions of this mission).
--
--   For a finite point cloud $L$ in a metric space, with $D$ the distance and $g=f|_L$, this is the diagram $D_0\mathcal R^f_\delta(L)$ of the paper; for $n$ sample points $x_1,\dots,x_n$ it is computed on the index set $\{1,\dots,n\}$ with $D_{ij}=d(x_i,x_j)$ and $g_i=f(x_i)$.
--
--   **Formalization Note** The edge relation is symmetrized (an edge when $D_{ij}\le\delta$ or $D_{ji}\le\delta$); every use has a symmetric matrix. Connected components of an induced subgraph are expressed by paths whose vertices all lie in $L^t$.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 9, Definition 2.1 and Eqs. (2)–(3)

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

noncomputable section

variable {ι : Type*}

/-- Definition 2.1: the Rips graph `R_δ` on the vertex set `ι` with distance matrix `Dm`: `i` and
`j ≠ i` are adjacent when `Dm i j ≤ δ` (or `Dm j i ≤ δ`; `Dm` is symmetric in every use). -/
def ripsGraph (Dm : ι → ι → ℝ) (δ : ℝ) : SimpleGraph ι :=
  SimpleGraph.fromRel (fun i j => Dm i j ≤ δ)

/-- `i` and `j` lie in the same connected component of `R_δ(L^t)`, the subgraph of the Rips graph
induced on the vertices `L^t = {i | t ≤ g i}` (Eq. (2)): `i ∈ L^t` and `j` is reached from `i` by a
path of Rips edges whose endpoints all lie in `L^t`. -/
def ripsJoined (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) (t : ℝ) (i j : ι) : Prop :=
  t ≤ g i ∧ Relation.ReflTransGen (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) i j

/-- The rank function of the upper-star Rips filtration `𝓡^g_δ(L) = {R_δ(L^α)}_α` (Eq. (3)): for
`t ≤ s`, the number of connected components of `R_δ(L^t)` that contain a vertex of `L^s`. -/
def ripsRank (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) : ℝ → ℝ → ℕ∞ :=
  rankFn (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ)

/-- The 0-th persistence diagram `D₀𝓡^g_δ(L)` of the upper-star Rips filtration. -/
def ripsDiagram (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) : EReal × EReal → ℕ∞ :=
  mult (ripsRank Dm g δ)

end

end PersistClust.Count


