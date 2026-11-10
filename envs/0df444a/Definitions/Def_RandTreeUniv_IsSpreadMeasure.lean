-- Prove2me | Definitions.Def_RandTreeUniv_IsSpreadMeasure
-- name    : RandTreeUniv_IsSpreadMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:15.480581+00:00
-- url     : https://prove2.me/theorems/f8b7df43-6ffd-4457-b186-4c1fb0038c36
-- title:
--   $q$-spread probability measure (Definition 2.15) and $\ell(F)$
-- statement:
--   Let $X$ be a finite set and $F\subseteq 2^X$ a family of subsets. For $S\subseteq X$ the **up-set** of $S$ is $\langle S\rangle=\{A\cup S:A\subseteq X\}$, so $F\cap\langle S\rangle=\{A\in F: S\subseteq A\}$. For $q\in(0,1)$, a probability measure $\nu$ on $F$ is **$q$-spread** if for every $S\subseteq X$
--
--   $$
--   \nu\big(F\cap\langle S\rangle\big)\le q^{|S|} .
--   $$
--
--   That is, a $\nu$-random member of $F$ contains any fixed set $S$ with probability at most $q^{|S|}$. The module also defines $\ell(F)$, the maximal size of a minimal element of $F$ (minimal with respect to inclusion among members of $F$), with $\ell(\emptyset)=0$.
--
--   Spread measures are the hypothesis of the fractional expectation-threshold theorem (Theorem 2.16).
--
--   **Formalization Note** $\nu$ is a weight function of which only the values on $F$ matter; it is nonnegative on $F$ and sums to $1$ over $F$. The condition $q\in(0,1)$ is part of the predicate.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §2.6 and Definition 2.15, p.13 (PDF 14); ℓ(F) from Theorem 2.16, p.13 (PDF 14)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- A `q`-spread probability measure on a family `F ⊆ 2^X` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §2.6 and Definition 2.15,
p.13 (PDF 14)). For `q ∈ (0, 1)`, a probability measure `ν` on `(F, 2^F)` is `q`-spread if, for
every `S ⊆ X`, `ν(F ∩ ⟨S⟩) ≤ q^{|S|}`, where `⟨S⟩ = {A ∪ S : A ⊆ X}` is the up-set of `S`, so
`F ∩ ⟨S⟩ = {A ∈ F : S ⊆ A}`.

**Formalization Note** `X` is a finite type and `F : Finset (Finset X)`. The measure is a weight
function `ν : Finset X → ℝ` of which only the values on `F` are used: nonnegative on `F`, summing
to `1` over `F`. The range `q ∈ (0, 1)` of the definition is part of the predicate. -/
def IsSpreadMeasure {X : Type*} [Fintype X] (F : Finset (Finset X)) (q : ℝ)
    (ν : Finset X → ℝ) : Prop :=
  0 < q ∧ q < 1 ∧ (∀ A ∈ F, 0 ≤ ν A) ∧ (∑ A ∈ F, ν A = 1) ∧
    ∀ S : Finset X, ∑ A ∈ F.filter (fun A => S ⊆ A), ν A ≤ q ^ S.card

/-- `ℓ(F)`, the maximal size of a minimal element of `F` (minimal for inclusion within `F`)
(Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), Theorem 2.16, p.13 (PDF 14)). It is `0` for the empty family. -/
noncomputable def maxMinimalSize {X : Type*} (F : Finset (Finset X)) : ℕ :=
  (F.filter fun A => ∀ B ∈ F, B ⊆ A → B = A).sup Finset.card

end RandTreeUniv


