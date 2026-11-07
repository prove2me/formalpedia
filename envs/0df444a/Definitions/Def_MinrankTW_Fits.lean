-- Prove2me | Definitions.Def_MinrankTW_Fits
-- name    : MinrankTW_Fits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:45.913371+00:00
-- url     : https://prove2.me/theorems/1346f720-7353-4f57-827d-5d6cc36bc594
-- title:
--   Matrix fitting a graph
-- statement:
--   Let $G$ be a simple graph on $[n]=\{1,\dots,n\}$ and $\mathbb F$ a field. A matrix $M\in\mathbb F^{n\times n}$ **fits** $G$ if
--   $$
--   M_{ii}\neq 0\quad(i\in[n]),\qquad M_{ij}=0\quad(i\neq j,\ ij\notin E(G)).
--   $$
--   The matrix need not be symmetric: for an edge $ij$ the entries $M_{ij}$ and $M_{ji}$ are unconstrained and independent of each other.
--
--   Fitting matrices are the feasible set of the minrank problem and, through the index-coding reduction, the scalar linear index codes of the knowledge graph $G$.
--
--   **Formalization Note** The vertex set $[n]$ is `Fin n`.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1, p.2

import Mathlib

namespace MinrankTW

/-- A matrix `M ∈ F^{n×n}` **fits** the graph `G` on `[n]` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1, p.2):
`M_ii ≠ 0` for every `i`, and `M_ij = 0` whenever `i ≠ j` and `ij ∉ E(G)`.

**Formalization Note** The vertex set `[n]` is `Fin n`. `M` need not be symmetric (p.2):
the entries `M_ij` and `M_ji` of an edge are unconstrained and independent. -/
def Fits {F : Type*} [Field F] {n : ℕ} (G : SimpleGraph (Fin n)) (M : Matrix (Fin n) (Fin n) F) :
    Prop :=
  (∀ i, M i i ≠ 0) ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → M i j = 0

end MinrankTW


