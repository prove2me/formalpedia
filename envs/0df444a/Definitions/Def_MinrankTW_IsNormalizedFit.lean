-- Prove2me | Definitions.Def_MinrankTW_IsNormalizedFit
-- name    : MinrankTW_IsNormalizedFit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:41.753907+00:00
-- url     : https://prove2.me/theorems/79a38b86-8c2b-4cd9-990d-3ba0dfbad2d3
-- title:
--   Normalized fitting matrix
-- statement:
--   A matrix $M\in\mathbb F^{n\times n}$ is a **normalized** fitting matrix of the graph $G$ if it fits $G$ and all its diagonal entries equal one: $M_{ii}=1$ for every $i$.
--
--   Scaling rows turns every fitting matrix into a normalized one of the same rank. Theorem 1 counts normalized fitting matrices; their number of each rank is the corresponding coefficient of $Z_G(z)$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1, p.2 and Section 1.2, p.4

import Mathlib
import Definitions.Def_MinrankTW_Fits

namespace MinrankTW

/-- A **normalized** fitting matrix (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1, p.2, and §1.2, p.4): `M` fits `G` and all
its diagonal entries equal one. -/
def IsNormalizedFit {F : Type*} [Field F] {n : ℕ} (G : SimpleGraph (Fin n))
    (M : Matrix (Fin n) (Fin n) F) : Prop :=
  Fits G M ∧ ∀ i, M i i = 1

end MinrankTW


