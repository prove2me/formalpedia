-- Prove2me | Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate
-- name    : SumsHighPowers_PITLifting_PairwiseNonAssociate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:09:48.445402+00:00
-- url     : https://prove2.me/theorems/1ad78c7e-7722-4024-956b-94a6ac6848b3
-- title:
--   Pairwise non-associate polynomials = pairwise linearly independent (p. 12)
-- statement:
--   Let $F$ be a field. Two nonzero polynomials $f,g$ are **associate** if $g=\alpha f$ for a nonzero scalar $\alpha\in F$, and non-associate otherwise. A family of polynomials is **(pairwise) non-associate** if no two of its members are associate; the paper notes (§1.5, p. 12) that this is equivalent to the members being **pairwise linearly independent**, and this definition takes that form: for a family $(f_i)_{i\in\iota}$,
--   $$\forall i\neq j:\quad f_i,\ f_j\ \text{are linearly independent over } F .$$
--   In particular, in a family with at least two members, every member is nonzero and no two members are equal.
--
--   **Formalization Note.** Stated for a family in any $F$-module (used for $F[x]$ and $F[x_1,\dots,x_n]$): `∀ i j, i ≠ j → LinearIndependent F ![f i, f j]`.
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 12, §1.5 (associate, non-associate, pairwise linearly independent)

import Mathlib

namespace SumsHighPowers.PITLifting

/-- **Pairwise non-associate family** (Kaplan–Shpilka–Tal, §1.5, p. 12): nonzero `f, g` are associate
if `g = α f` for a nonzero scalar `α`; a set of polynomials is non-associate if no two of its members
are associate, "equivalent to saying that the polynomials in the set are pairwise linearly
independent". This definition is the paper's equivalent form: any two members with distinct indices
are linearly independent over `F`.

**Formalization Note.** Stated for a family `f : ι → M` of vectors in an `F`-module (used for
`F[x]` and `F[x₁, …, xₙ]`). Pairwise linear independence also forces every member to be nonzero
when the family has at least two members. -/
def PairwiseNonAssociate {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {ι : Type*} (f : ι → M) : Prop :=
  ∀ i j, i ≠ j → LinearIndependent F ![f i, f j]

end SumsHighPowers.PITLifting


