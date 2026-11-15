-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial
-- name    : ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:20:45.683228+00:00
-- url     : https://prove2.me/theorems/c765565c-d652-4558-ad04-b5b5d7741b86
-- title:
--   Adversarial generation in the limit (with or without repetition)
-- statement:
--   Let $C$ be a collection of infinite languages over a universe $U$ and $q\in\{\mathrm R,\mathrm{NR}\}$ a repetition convention. A generator $G$ **adversarially generates $C$ in the limit** under $q$ if for every language $L\in C$ and **every** full, repetition-free enumeration $x_1,x_2,\ldots$ of $L$ there is a finite time $t^\star\ge1$ such that
--
--   $$
--   G(x_1,\ldots,x_t)\ \text{is } q\text{-correct for } L \text{ at every } t\ge t^\star .
--   $$
--
--   The time $t^\star$ may depend on both $L$ and the enumeration. A collection is adversarially generatable in the limit under $q$ if some generator does this. These are the classes $\mathrm{Adv}_{\mathrm R}$ and $\mathrm{Adv}_{\mathrm{NR}}$; the generator-level predicate is needed separately for the stabilisation lemma (Lemma 3.10).
--
--   **Formalization Note** Correctness is the published `CorrectAt` of the base mission (NR excludes every earlier output, including incorrect ones). Stream index $n$ is time $t=n+1$.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Definitions 2.6, 2.7, printed p.5–6 (PDF p.6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Definition 2.6 with Definition 2.7, printed pp.5–6 (PDF pp.6–7): the generator `G` is
eventually correct, under convention `mode`, on every full injective enumeration of every
language of `C`; the success time may depend on the language and on the enumeration. -/
def AdvGenerates {U : Type} (mode : Repetition) (G : Generator U)
    (C : LanguageCollection U) : Prop :=
  ∀ L ∈ C, ∀ x : ℕ → U, IsEnumeration L x →
    ∃ tStar : ℕ, 0 < tStar ∧ ∀ n : ℕ, tStar ≤ n + 1 → CorrectAt mode G L x n

/-- `C` is adversarially generatable in the limit under convention `mode`. -/
def AdversarialLimitGeneratable {U : Type} (mode : Repetition)
    (C : LanguageCollection U) : Prop :=
  ∃ G : Generator U, AdvGenerates mode G C

end ActiveLanguageGeneration.Hierarchy.Supplement


