-- Prove2me | Definitions.Def_MinrankTW_Supplement_IdentifiableRows
-- name    : MinrankTW_Supplement_IdentifiableRows
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:05:47.813858+00:00
-- url     : https://prove2.me/theorems/3c042b59-fad6-42f4-ab3d-b9a477409bfe
-- title:
--   Uniquely identifiable basis rows; vertex degrees
-- statement:
--   Let $G$ be a graph on $[n]$ and $M\in\mathbb F^{n\times n}$ with row space $U=\operatorname{span}\{M_1,\dots,M_n\}$, where $M_i$ is row $i$. A set $J\subseteq[n]$ indexes **uniquely identifiable basis rows** of $M$ if
--
--   1. the rows $M_i$, $i\in J$, form a basis of $U$, and
--   2. for each $i\in J$, $M_i$ is the only vector $x\in U$ satisfying the normalized fitting constraints for vertex $i$:
--   $$
--   x_i=1,\qquad x_j=0\ \text{ for every } j\ne i \text{ with } ij\notin E(G).
--   $$
--
--   The **degree** $\deg_G(i)$ is the number of neighbours of $i$, and $\deg(G)$ is the maximum degree ($0$ for the empty vertex set).
--
--   For a normalized fitting matrix, condition 2 says $(e_i+E_i)\cap U=\{M_i\}$, equivalently $U\cap E_i=\{0\}$, where $E_i$ is the space of vectors supported on the neighbours of $i$ (Eq. (31)). This is the hypothesis of Theorem 7.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), §D, p.22 (uniquely identifiable basis rows), §D.2, p.23, Eq. (31)

import Mathlib

namespace MinrankTW.Supplement

open Classical in
/-- The degree `deg_G(i)` of vertex `i`: its number of neighbours (Perles–Weinstein, *Efficient
Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript
(sha256 32a91384…c57991), §D.2, p.23: `d_i = dim E_i = deg_G(i)`). -/
noncomputable def deg {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => G.Adj i j).card

/-- The maximum degree `deg(G)` (Theorem 7, p.22); `0` for the empty graph. -/
noncomputable def maxDeg {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (deg G)

/-- **Uniquely identifiable basis rows** (Perles–Weinstein, STOC 2027 submission manuscript
(sha256 32a91384…c57991), §D, p.22: "its row space has a basis of rows M*_i, each the unique vector
in row M* satisfying the normalized fitting constraints for vertex i"; p.23, Eq. (31)). For a
matrix `M` with row space `U = span {M_i}` and `J ⊆ [n]`:
1. the rows `M_i`, `i ∈ J`, are linearly independent and span `U`;
2. for each `i ∈ J`, `M_i` is the only `x ∈ U` with `x_i = 1` and `x_j = 0` for every `j ≠ i`
   with `ij ∉ E(G)`.

**Formalization Note** Row `i` of `M` is the vector `M i : Fin n → F`. Condition 2 is
`(e_i + E_i) ∩ U = {M_i}`, equivalently `U ∩ E_i = {0}` when `M` is a normalized fitting matrix. -/
def HasIdentifiableBasisRows {F : Type*} [Field F] {n : ℕ} (G : SimpleGraph (Fin n))
    (M : Matrix (Fin n) (Fin n) F) (J : Finset (Fin n)) : Prop :=
  LinearIndependent F (fun i : J => M i) ∧
  Submodule.span F (Set.range fun i : J => M i) = Submodule.span F (Set.range fun i => M i) ∧
  ∀ i ∈ J, ∀ x ∈ Submodule.span F (Set.range fun i => M i),
    x i = 1 → (∀ j, j ≠ i → ¬ G.Adj i j → x j = 0) → x = M i

end MinrankTW.Supplement


