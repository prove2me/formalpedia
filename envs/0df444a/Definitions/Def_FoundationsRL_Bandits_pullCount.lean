-- Prove2me | Definitions.Def_FoundationsRL_Bandits_pullCount
-- name    : FoundationsRL_Bandits_pullCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:55:26.972721+00:00
-- url     : https://prove2.me/theorems/19c361c2-df5f-4e52-a149-ac4f1d5d4787
-- title:
--   Pull count: number of times a decision has been selected
-- statement:
--   For a decision space $\Pi = \{1,\dots,A\}$ and a realized sequence of decisions
--   $\pi_1,\pi_2,\dots$ (one per round of the multi-armed bandit protocol), the **pull
--   count** $n_t(\pi)$ counts how many times decision $\pi \in \Pi$ has been selected
--   strictly before round $t$:
--
--   $$n_t(\pi) := \bigl|\{\, s < t : \pi_s = \pi \,\}\bigr|.$$
--
--   This is Foster & Rakhlin's $n_t(\pi)$, used throughout §2.2–2.3 to control the
--   number of samples the empirical mean $\hat f_t(\pi)$ (Eq. (2.5)) averages over, and
--   hence the width of any confidence interval built from it.
--
--   **Formalization Note.** Rounds are indexed from $0$ in Lean (`t : ℕ`), so
--   `pullCount pi t a` counts occurrences among rounds $0,\dots,t-1$, matching the
--   book's $n_t(\pi)$ under a 0-based reindexing of $t = 1,\dots,T$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 23, Eq. (2.5) and footnote 5

import Mathlib

namespace FoundationsRL.Bandits

/-- The number of times decision `a` has been selected strictly before round `t`,
`n_t(π) := |{s < t : π_s = π}|` (Foster–Rakhlin, p. 23, following Eq. (2.5)),
for a realized decision sequence `pi : ℕ → Fin A`. -/
def pullCount {A : ℕ} (pi : ℕ → Fin A) (t : ℕ) (a : Fin A) : ℕ :=
  ((Finset.range t).filter (fun s => pi s = a)).card

end FoundationsRL.Bandits


