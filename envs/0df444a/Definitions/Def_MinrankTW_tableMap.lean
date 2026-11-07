-- Prove2me | Definitions.Def_MinrankTW_tableMap
-- name    : MinrankTW_tableMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:11.732096+00:00
-- url     : https://prove2.me/theorems/6dfda826-08f4-48c6-b9bf-d3a083f2d12d
-- title:
--   Linear transform of tables with a 0/1 matrix
-- statement:
--   For a 0/1 matrix $k$ indexed by a finite set $\iota$ (here: linear relations, or subspaces), the corresponding linear transform of tables $f:\iota\to A$ is
--   $$
--   (Kf)(i)=\sum_{j:\,k(i,j)} f(j).
--   $$
--   The **transpose** of this transform is the transform of the transposed matrix, $(K^{\mathsf T}f)(i)=\sum_{j:\,k(j,i)}f(j)$; this is the sense of "transpose" in Section 4.3.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4.3, p.14

import Mathlib

namespace MinrankTW

/-- The linear transform on tables with 0/1 matrix `k` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §4.3, p.14: "a transpose refers
to the matrix of the corresponding linear transform on tables"): `(K f)(i) = ∑_{j : k i j} f j`.
The transpose of this transform is `tableMap (fun i j => k j i)`.

**Formalization Note** Tables are functions `ι → A` into an additive commutative monoid; the
sum is a `finsum`, the finite sum on the finite index sets (linear relations, subspaces) used in
this development. -/
noncomputable def tableMap {ι A : Type*} [AddCommMonoid A] (k : ι → ι → Prop) (f : ι → A)
    (i : ι) : A :=
  ∑ᶠ (j : ι) (_ : k i j), f j

end MinrankTW


