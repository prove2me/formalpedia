-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
-- name    : SubsamplingSM_Offline_IsMinRemoval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:18.979372+00:00
-- url     : https://prove2.me/theorems/d903440b-f074-41cb-b6a9-071115544d88
-- title:
--   Selection rule for the smallest removal set $O_u$
-- statement:
--   Line 6 of Algorithm 2 takes $O_u\subseteq O\setminus S$ to be "the smallest set such that $O\setminus O_u\in\mathcal I$". A **minimum-removal rule** is a function $\mathrm{sel}(O,S)$ such that, for all $O$ and $S$,
--   1. $\mathrm{sel}(O,S)\subseteq O\setminus S$, and
--   2. whenever some $Y\subseteq O\setminus S$ has $O\setminus Y\in\mathcal I$, the set $\mathrm{sel}(O,S)$ is such a set of minimum cardinality: $O\setminus\mathrm{sel}(O,S)\in\mathcal I$ and $|\mathrm{sel}(O,S)|\le|Y|$ for every such $Y$.
--
--   **Formalization Note** The page does not say which smallest set is taken when there are several, so Algorithm 2 takes the rule as a parameter and the lemmas hold for every minimum-removal rule. Such rules exist for every $\mathcal I$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 2, Line 6, p. 9

import Mathlib

namespace SubsamplingSM.Offline

/-- **A selection rule for the smallest removal set `O_u`.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 2, Line 6, p. 9: "Let `Ou ⊆ O \ S` be the smallest set such that
`O \ Ou ∈ I`."

`IsMinRemoval I sel` says that the rule `sel` always returns a subset of `O \ S` and that,
whenever some `Y ⊆ O \ S` has `O \ Y ∈ I`, `sel O S` is such a set of minimum cardinality.

**Formalization Note.** Line 6 does not say which smallest set is taken when several have the
minimum size, so Algorithm 2 takes the rule as a parameter and the statements hold for every
rule of this kind (paper.md generalization 8). In every run such a set exists (`Y = O \ S`
works, Lemma 5's proof, p. 11), so the hypothesis only fixes the choice. -/
def IsMinRemoval {α : Type*} [DecidableEq α] (I : Finset α → Prop)
    (sel : Finset α → Finset α → Finset α) : Prop :=
  ∀ O S : Finset α, sel O S ⊆ O \ S ∧
    ((∃ Y ⊆ O \ S, I (O \ Y)) →
      I (O \ sel O S) ∧ ∀ Y ⊆ O \ S, I (O \ Y) → (sel O S).card ≤ Y.card)

end SubsamplingSM.Offline


