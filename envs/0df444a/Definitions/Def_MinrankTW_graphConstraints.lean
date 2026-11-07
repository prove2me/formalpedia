-- Prove2me | Definitions.Def_MinrankTW_graphConstraints
-- name    : MinrankTW_graphConstraints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:46.345683+00:00
-- url     : https://prove2.me/theorems/b208f694-6027-4d4a-83f9-e922ebc0d596
-- title:
--   Entry constraints of graph minrank
-- statement:
--   For a graph $G$ on $[n]$ over $\mathbb F_q$, the entry constraints of graph minrank are
--   $$
--   S_{ii}=\{1\},\qquad S_{ij}=\mathbb F_q\ \ (ij\in E(G)),\qquad S_{ij}=\{0\}\ \text{otherwise}.
--   $$
--   The choices of $M_{ij}$ and $M_{ji}$ are independent. The completions are the normalized fitting matrices of $G$, and the rank enumerator is $Z_G(z)$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1.2, p.5

import Mathlib

namespace MinrankTW

/-- The entry constraints of graph minrank (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1.2, p.5): `S_ii = {1}`, `S_ij = F_q`
when `ij ∈ E(G)`, and `S_ij = {0}` otherwise. Their completions are the normalized fitting
matrices of `G`, and their rank enumerator is `Z_G(z)`.

**Formalization Note** The choices of `M_ij` and `M_ji` are independent: `S_ij` and
`S_ji` are separate entries. Adjacency is decided classically. -/
noncomputable def graphConstraints (F : Type*) [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fin n → Fin n → Finset F := by
  classical
  exact fun i j => if i = j then {1} else if G.Adj i j then Finset.univ else {0}

end MinrankTW


