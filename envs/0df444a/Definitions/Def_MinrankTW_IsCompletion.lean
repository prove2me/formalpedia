-- Prove2me | Definitions.Def_MinrankTW_IsCompletion
-- name    : MinrankTW_IsCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:45.133384+00:00
-- url     : https://prove2.me/theorems/f0d8a261-fe0a-46de-b497-af9324f5f407
-- title:
--   Completion of independent entry constraints
-- statement:
--   Let $S=(S_{ij})_{i\in[m],j\in[n]}$ be a family of subsets of $\mathbb F_q$ (independent entry constraints). A **completion** of $S$ is a matrix $M\in\mathbb F_q^{m\times n}$ with
--   $$
--   M_{ij}\in S_{ij}\qquad\text{for every } i,j.
--   $$
--
--   **Formalization Note** The allowed sets are finite sets of field elements. The source requires every $S_{ij}$ to be nonempty; this predicate does not, and the theorems that need nonemptiness assume it.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1.2, p.5

import Mathlib

namespace MinrankTW

/-- A **completion** of the independent entry constraints `S = (S_ij)` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1.2, p.5):
a matrix `M ∈ F^{m×n}` with `M_ij ∈ S_ij` for every `i, j`.

**Formalization Note** The allowed sets are `Finset`s of the finite field. The paper's standing
requirement that every `S_ij` is nonempty is not part of this predicate; the theorems that need
it carry it as a hypothesis. -/
def IsCompletion {F : Type*} {m n : ℕ} (S : Fin m → Fin n → Finset F)
    (M : Matrix (Fin m) (Fin n) F) : Prop :=
  ∀ i j, M i j ∈ S i j

end MinrankTW


