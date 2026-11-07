-- Prove2me | Definitions.Def_MinrankTW_joinConv
-- name    : MinrankTW_joinConv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:51.630305+00:00
-- url     : https://prove2.me/theorems/0ba62890-8fb2-47f0-87ca-7bf087dc3ad8
-- title:
--   Join convolution of relation tables
-- statement:
--   For two tables $f,g$ on the linear relations in $\mathbb F^a\oplus\mathbb F^c$ with values in a commutative semiring, their join convolution is
--   $$
--   h(R)=\sum_{R_1\boxplus R_2=R} f(R_1)\,g(R_2).
--   $$
--   At a join node of the dynamic program the table is the join convolution of the children's tables (Eq. (10)); Lemma 2 and Proposition 1 compute it fast.
--
--   **Formalization Note** The sum is over all pairs of subspaces of the finite space $\mathbb F^a\oplus\mathbb F^c$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 2.3, p.8, Eq. (10); Lemma 2, p.13

import Mathlib
import Definitions.Def_MinrankTW_relJoin

namespace MinrankTW

/-- The **join convolution** of two tables on linear relations (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §2.3, p.8, Eq. (10), and
Lemma 2, p.13): `h(R) = ∑_{R₁ ⊞ R₂ = R} f(R₁) g(R₂)`.

**Formalization Note** Tables take values in any commutative semiring `A`. The sum is a
`finsum` over pairs of submodules; the space `(α → F) × (γ → F)` is finite for finite `F`,
`α`, `γ`, so there are finitely many linear relations and the `finsum` is the finite sum. -/
noncomputable def joinConv {F : Type*} [Field F] {α γ : Type*} {A : Type*} [CommSemiring A]
    (f g : Submodule F ((α → F) × (γ → F)) → A) (R : Submodule F ((α → F) × (γ → F))) : A :=
  ∑ᶠ (R₁ : Submodule F ((α → F) × (γ → F))) (R₂ : Submodule F ((α → F) × (γ → F)))
    (_ : relJoin R₁ R₂ = R), f R₁ * g R₂

end MinrankTW


