-- Prove2me | Definitions.Def_ProjLikeRetr_FixedRank_rankSet
-- name    : ProjLikeRetr_FixedRank_rankSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:42:04.776503+00:00
-- url     : https://prove2.me/theorems/6250e1ec-02e4-49e7-84a3-4af13b70fdfb
-- title:
--   §3.2, pp. 8–9 — the fixed-rank set ℛ_r = {rank X = r} and the set {rank X ≤ r}
-- statement:
--   For natural numbers $n, m, r$ the set of real $n\times m$ matrices of **fixed rank** $r$ is
--
--   $$\mathcal R_r=\{X\in\mathbb R^{n\times m}:\ \operatorname{rank}(X)=r\},$$
--
--   and the set of matrices of rank **at most** $r$ is
--
--   $$\{X\in\mathbb R^{n\times m}:\ \operatorname{rank}(X)\le r\}.$$
--
--   The first is the smooth submanifold of $\mathbb R^{n\times m}$ studied in §3.2 and §4.4 of the paper; the second is the closed algebraic set onto which the truncated singular value decomposition projects (the Eckart–Young result (3.7)). Keeping both sets explicit is what allows the mission to separate "rank equal to $r$" (Proposition 3.3) from "rank at most $r$" (Eckart–Young).
--
--   **Formalization Note** The file defines `rankSet r` ($\mathcal R_r$) and `rankLeSet r` (rank $\le r$) as sets of `Matrix ι κ ℝ` for arbitrary row and column index types with finitely many columns; $\mathbb R^{n\times m}$ is the case `ι = Fin n`, `κ = Fin m`, and §4.4 uses the block index types `Fin r ⊕ Fin p`, `Fin r ⊕ Fin q`. The rank is Mathlib's `Matrix.rank`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 8, §3.2 (definition of ℛ_r); p. 9, §3.2 (the set of matrices with rank ≤ r, before (3.7))

import Mathlib

namespace ProjLikeRetr.FixedRank

/-- §3.2, p. 8: the set `ℛ_r = {X ∈ ℝ^{n×m} : rank(X) = r}` of real matrices of rank exactly `r`.
Rows and columns are indexed by arbitrary finite types `ι`, `κ` (`Fin n`, `Fin m` for `ℝ^{n×m}`;
block index types `Fin r ⊕ Fin p` in §4.4). -/
def rankSet {ι κ : Type*} [Fintype κ] (r : ℕ) : Set (Matrix ι κ ℝ) :=
  {X | X.rank = r}

/-- §3.2, p. 9: the (closed, algebraic) set `{X ∈ ℝ^{n×m} : rank(X) ≤ r}` of real matrices of rank at
most `r`, onto which (3.7) projects. -/
def rankLeSet {ι κ : Type*} [Fintype κ] (r : ℕ) : Set (Matrix ι κ ℝ) :=
  {X | X.rank ≤ r}

end ProjLikeRetr.FixedRank


