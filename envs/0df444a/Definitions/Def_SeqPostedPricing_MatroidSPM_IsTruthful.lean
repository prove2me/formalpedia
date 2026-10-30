-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsTruthful
-- name    : SeqPostedPricing_MatroidSPM_IsTruthful
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:31:03.504828+00:00
-- url     : https://prove2.me/theorems/711fd10a-d3d9-4a40-b806-4ae1aab255b4
-- title:
--   Truthful (dominant-strategy incentive compatible) mechanism
-- statement:
--   A mechanism $M$ is **truthful** if no agent can gain by misreporting, whatever the others report: for every value profile $\mathbf v$, every agent $i$ and every report $w\in\mathbb R$,
--
--   $$
--   u_i\big(v_i;(w,\mathbf v_{-i})\big)\le u_i(v_i;\mathbf v).
--   $$
--
--   This is the notion of truthfulness under which Myerson's mechanism and all posted-price mechanisms are truthful.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.3 (Lemma 2), p. 5; App. A (Theorem 19), p. 12

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_utility

namespace SeqPostedPricing.MatroidSPM

/-- **Truthful (dominant-strategy incentive compatible) mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.1–2.3, pp. 4–5 (PDF pp. 6–7) ("truthful mechanism", Lemma 2, Theorem 19).

`IsTruthful M`: for every value profile `v`, every agent `i` and every misreport `w`, agent `i`
does not gain by reporting `w` instead of `v i`, whatever the others report.

**Formalization Note.** Truthfulness is in dominant strategies and ex post, the notion under
which Myerson's mechanism and posted-price mechanisms are truthful. -/
def IsTruthful {n : ℕ} (M : Mechanism n) : Prop :=
  ∀ (v : Fin n → ℝ) (i : Fin n) (w : ℝ),
    utility M i (v i) (Function.update v i w) ≤ utility M i (v i) v

end SeqPostedPricing.MatroidSPM


