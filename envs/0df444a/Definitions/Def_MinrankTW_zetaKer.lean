-- Prove2me | Definitions.Def_MinrankTW_zetaKer
-- name    : MinrankTW_zetaKer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:10.178935+00:00
-- url     : https://prove2.me/theorems/b2859755-7d76-428a-af6a-2705c5cf0a0e
-- title:
--   Subspace zeta transform
-- statement:
--   The **subspace zeta transform** of a table $f$ on the subspaces of a vector space is
--   $$
--   (Zf)(R)=\sum_{S\le R} f(S);
--   $$
--   its transpose $(Z^{\mathsf T}f)(R)=\sum_{S\ge R}f(S)$ sums over superspaces. Theorem 4 computes both and their inverses fast.
--
--   **Formalization Note** Recorded as the 0/1 matrix $[S\le R]$, used with the generic table transform.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 4, p.8 and Section 4.3, p.13

import Mathlib

namespace MinrankTW

/-- The matrix of the **subspace zeta transform** (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 4, p.8, and §4.3, p.13):
`(Zf)(R) = ∑_{S ≤ R} f(S)`, i.e. entry `(R, S)` is `1` exactly when `S ≤ R`. With
`tableMap`, `tableMap zetaKer` is `Z` and `tableMap (fun R S => zetaKer S R)` is its
transpose `Zᵀ`, which sums over superspaces. -/
def zetaKer {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (R S : Submodule F V) : Prop :=
  S ≤ R

end MinrankTW


