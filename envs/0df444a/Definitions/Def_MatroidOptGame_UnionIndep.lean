-- Prove2me | Definitions.Def_MatroidOptGame_UnionIndep
-- name    : MatroidOptGame_UnionIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:44.702429+00:00
-- url     : https://prove2.me/theorems/880b7c96-9d05-48d7-89ed-01d48cc4a28e
-- title:
--   Independent set of the union $M \vee M$
-- statement:
--   For a matroid $M$ on $E$, a set $F \subseteq E$ is **independent in the matroid union** $M \vee M$ if
--   $$
--   F = I \cup J \quad \text{for some independent sets } I, J \text{ of } M .
--   $$
--   The paper defines $M \vee M'$ as the set system $(E, \mathcal I \vee \mathcal I')$ with $\mathcal I \vee \mathcal I' = \{F \cup F' : F \in \mathcal I,\ F' \in \mathcal I'\}$ and notes that it is a matroid.
--
--   **Formalization Note** Mathlib has no matroid union, so $M \vee M$ enters only through this family of independent sets. Since it is a matroid, its bases are exactly its maximum-size independent sets; the definitions of $r_{M\vee M}(E)$ and $w(B_{\min}(M \vee M, w))$ use this.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.20

import Mathlib

namespace MatroidOptGame

/-- `F` is independent in the matroid union `M ∨ M`: `F = I ∪ J` for two independent sets
`I, J` of `M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.20 ("The set system (E, I ∨ I′), where
I ∨ I′ = {F ∪ F′ : F ∈ I and F′ ∈ I′}, is a matroid, denoted M ∨ M′").

**Formalization Note.** Mathlib has no matroid union, so `M ∨ M` is used through this set
system. The paper notes that it is a matroid (p.20); its bases are therefore exactly its
maximum-size independent sets, which is how `unionRank` and `unionMinBaseWeight` use it. -/
def UnionIndep {α : Type*} [DecidableEq α] (M : Matroid α) (F : Finset α) : Prop :=
  ∃ I J : Finset α, M.Indep (I : Set α) ∧ M.Indep (J : Set α) ∧ F = I ∪ J

end MatroidOptGame


