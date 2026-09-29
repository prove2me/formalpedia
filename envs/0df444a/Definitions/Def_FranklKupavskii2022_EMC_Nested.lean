-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_Nested
-- name    : FranklKupavskii2022_EMC_Nested
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:14:52.431176+00:00
-- url     : https://prove2.me/theorems/6bcc5fc2-0a5b-49bd-864d-93dad27d89fa
-- title:
--   Nested families $\mathcal F_1\supseteq\dots\supseteq\mathcal F_{s+1}$
-- statement:
--   Families $\mathcal F_1,\dots,\mathcal F_{s+1}$ are **nested** if
--
--   $$
--   \mathcal F_1\supseteq\mathcal F_2\supseteq\dots\supseteq\mathcal F_{s+1}.
--   $$
--
--   For an initial family $\mathcal F$, the families $\mathcal F(\{1\}),\dots,\mathcal F(\{s+1\})$ are nested; this is how nestedness enters the proof.
--
--   **Formalization Note** The families are the values $1,\dots,s+1$ of a map $\mathbb N\to$ families; inclusions are non-strict.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 4, p. 9 (nested)

import Mathlib

namespace FranklKupavskii2022.EMC

/-- Nested families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 4, p. 9): "We say that
F_1, …, F_{s+1} are nested if F_1 ⊃ F_2 ⊃ … ⊃ F_{s+1}" (non-strict inclusions).

**Formalization Note.** The families are `Fam 1, …, Fam (s + 1)`; values of `Fam` outside
`1..s+1` are ignored. -/
def Nested (s : ℕ) (Fam : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ s + 1 → Fam j ⊆ Fam i

end FranklKupavskii2022.EMC


