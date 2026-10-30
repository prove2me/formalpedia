-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsIndividuallyRational
-- name    : SeqPostedPricing_MatroidSPM_IsIndividuallyRational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:31:42.130596+00:00
-- url     : https://prove2.me/theorems/7ffd848f-8068-44f5-921a-29d1bfe0a543
-- title:
--   Individually rational mechanism
-- statement:
--   A mechanism $M$ is **individually rational** if truthful participation never gives negative utility: for every value profile $\mathbf v$ and every agent $i$,
--
--   $$
--   u_i(v_i;\mathbf v)\ge 0 .
--   $$
--
--   In particular an agent that is not served pays nothing or receives a payment, and a served agent pays at most its value.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 3, p. 5; App. A, p. 12

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_utility

namespace SeqPostedPricing.MatroidSPM

/-- **Individually rational mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, Lemma 3, p. 5 (PDF p. 7) ("individually rational and truthful"); App. A, p. 12 (PDF p. 14):
"agents that are not served pay nothing".

`IsIndividuallyRational M`: every agent's utility under truthful reporting is nonnegative, at
every value profile.

**Formalization Note.** Ex-post individual rationality at every real value profile. Myerson's
mechanism satisfies it (served agents pay a threshold at most their value, the others pay
nothing). -/
def IsIndividuallyRational {n : ℕ} (M : Mechanism n) : Prop :=
  ∀ (v : Fin n → ℝ) (i : Fin n), 0 ≤ utility M i (v i) v

end SeqPostedPricing.MatroidSPM


