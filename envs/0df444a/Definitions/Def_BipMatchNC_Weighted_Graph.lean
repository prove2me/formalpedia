-- Prove2me | Definitions.Def_BipMatchNC_Weighted_Graph
-- name    : BipMatchNC_Weighted_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:12:14.949787+00:00
-- url     : https://prove2.me/theorems/7978c0fb-dcb3-47b8-8f64-b9fb055119da
-- title:
--   Balanced bipartite graphs on [n] + [n], perfect matchings as permutations, w*, W and the tight subgraph H (§2, §3.3)
-- statement:
--   A **balanced bipartite graph** $G=(L\cup R,E)$ with $L=\{u_1,\dots,u_n\}$, $R=\{v_1,\dots,v_n\}$ is given by its $n\times n$ bi-adjacency matrix $A=(a_{i,j})$, $a_{i,j}=1$ iff $(u_i,v_j)\in E$. A **perfect matching** is a permutation $\pi\in S_n$ with $(u_i,v_{\pi(i)})\in E$ for all $i$, and $G\in\mathrm{PM}$ if one exists. For weights $w(u_i,v_j)=w_{i,j}\in\mathbb N$, a **maximum weight perfect matching** is a perfect matching $\pi$ maximizing $\sum_i w_{i,\pi(i)}$, and
--   $$w^*=\max\{w(M): M \text{ a perfect matching of } G\},\qquad W=\max_{e\in E}w(e).$$
--   For a dual solution $(y,z)$, $H$ is the subgraph of $G$ consisting of the tight edges $y_{u_i}+z_{v_j}=w_{i,j}$.
--
--   **Formalization Note.** `BipGraph n` stores `adj : Fin n → Fin n → Bool`, with 0-based indices ($u_{i+1}$ is `i`). `IsPerfectMatching`, `HasPM`, `IsMaxWeightPM`, `maxPMWeight` ($w^*$, which is $0$ when there is no perfect matching; every statement using it assumes `HasPM`), `maxEdgeWeight` ($W$, $0$ for an edgeless graph) and `tightSubgraph` ($H$).
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 4 (PDF 5), §2 and §2.1; p. 14 (PDF 15) and p. 17 (PDF 18), §3.3

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite

namespace BipMatchNC.Weighted

/-- A **balanced bipartite graph** `G = (L ∪ R, E)` with `L = {u₁, …, u_n}` and `R = {v₁, …, v_n}`
(§2, p. 4), given by its `n × n` bi-adjacency matrix: `adj i j = true` iff `(u_i, v_j) ∈ E`.

**Formalization Note.** Vertices are indexed by `Fin n = {0, …, n - 1}`, so `u_{i+1}` is `i`. -/
structure BipGraph (n : ℕ) where
  /-- The bi-adjacency matrix `A = (a_{i,j})`. -/
  adj : Fin n → Fin n → Bool

namespace BipGraph

variable {n : ℕ}

/-- A **perfect matching** of a balanced bipartite graph, seen as the permutation `π_M ∈ S_n` with
`(u_i, v_{π(i)}) ∈ M` (§2.1, p. 4): every pair `(i, π i)` is an edge. -/
def IsPerfectMatching (G : BipGraph n) (π : Equiv.Perm (Fin n)) : Prop :=
  IsPerfectMatchingOn G.adj π

/-- `G ∈ PM`: `G` has a perfect matching (§2.1, p. 4). -/
def HasPM (G : BipGraph n) : Prop :=
  ∃ π, G.IsPerfectMatching π

/-- `π` is a **maximum weight perfect matching** of `G` for the weights `w(u_i, v_j) = w i j`:
a perfect matching whose weight `Σ_i w(i, π i)` is at least that of every perfect matching. -/
def IsMaxWeightPM (G : BipGraph n) (w : Fin n → Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  G.IsPerfectMatching π ∧
    ∀ σ, G.IsPerfectMatching σ → matchingWeight w σ ≤ matchingWeight w π

/-- `w*`: the weight of a maximum weight perfect matching of `G` (§3.3, p. 14). It is `0` when `G`
has no perfect matching; every statement using it assumes `G.HasPM`. -/
def maxPMWeight (G : BipGraph n) (w : Fin n → Fin n → ℕ) : ℕ :=
  maxPerfectMatchingWeight G.adj w

/-- `W`: the maximum weight of any edge of `G` (§3.3, p. 14); `0` when `G` has no edge. -/
def maxEdgeWeight (G : BipGraph n) (w : Fin n → Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun e : Fin n × Fin n => G.adj e.1 e.2 = true).sup fun e => w e.1 e.2

open Classical in
/-- The subgraph `H` of `G` consisting of the edges that are tight for the dual solution `(y, z)`
(§3.3, p. 17). -/
noncomputable def tightSubgraph (G : BipGraph n) (w : Fin n → Fin n → ℕ) (y z : Fin n → ℝ) :
    BipGraph n :=
  ⟨fun i j => decide (IsTight G.adj w y z i j)⟩

end BipGraph

end BipMatchNC.Weighted


