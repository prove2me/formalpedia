-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_CrossDependent
-- name    : FranklKupavskii2022_EMC_CrossDependent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:14:32.892839+00:00
-- url     : https://prove2.me/theorems/92ebbd48-82a8-4002-9ed0-b619278a8a0d
-- title:
--   Cross-dependent families $\mathcal F_1,\dots,\mathcal F_{s+1}$
-- statement:
--   Families $\mathcal F_1,\dots,\mathcal F_{s+1}$ of sets are **cross-dependent** if there are no
--
--   $$
--   F_1\in\mathcal F_1,\ \dots,\ F_{s+1}\in\mathcal F_{s+1}
--   $$
--
--   such that $F_1,\dots,F_{s+1}$ are pairwise disjoint. For $\mathcal F_1=\dots=\mathcal F_{s+1}=\mathcal F$ this is (up to repeated empty sets) the condition $\nu(\mathcal F)\le s$; the multi-family version is what the paper's key averaging lemma is about.
--
--   **Formalization Note** The families are the values $1,\dots,s+1$ of a map $\mathbb N\to$ families; other values are ignored. Disjointness is required between the sets chosen at distinct indices.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 4, p. 9 (cross-dependent)

import Mathlib

namespace FranklKupavskii2022.EMC

/-- Cross-dependent families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 4, p. 9): "families
F_1, …, F_{s+1} are cross-dependent, if there are no F_1 ∈ F_1, …, F_{s+1} ∈ F_{s+1} such that
F_1, …, F_{s+1} are pairwise disjoint."

**Formalization Note.** The `s + 1` families are `Fam 1, …, Fam (s + 1)` for
`Fam : ℕ → Finset (Finset ℕ)` (values outside `1..s+1` are ignored). Pairwise disjointness is
indexed by position: a choice `f i ∈ Fam i` with `f i` and `f j` disjoint for all `i ≠ j` in
`1..s+1` (so two chosen sets can only coincide if both are empty). -/
def CrossDependent (s : ℕ) (Fam : ℕ → Finset (Finset ℕ)) : Prop :=
  ¬ ∃ f : ℕ → Finset ℕ, (∀ i ∈ Finset.Icc 1 (s + 1), f i ∈ Fam i) ∧
    ∀ i ∈ Finset.Icc 1 (s + 1), ∀ j ∈ Finset.Icc 1 (s + 1), i ≠ j → Disjoint (f i) (f j)

end FranklKupavskii2022.EMC


