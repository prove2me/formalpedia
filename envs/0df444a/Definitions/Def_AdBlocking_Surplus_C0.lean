-- Prove2me | Definitions.Def_AdBlocking_Surplus_C0
-- name    : AdBlocking_Surplus_C0
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:14.245688+00:00
-- url     : https://prove2.me/theorems/6542f563-0ea4-462b-b1bd-e7f033fdf870
-- title:
--   Benchmark consumer-surplus multiplier C₀
-- statement:
--   The coefficient $C_0(r,t)$ multiplies quality in benchmark consumer surplus. On the branch $t\le r/(1+r)$, it is
--
--   $$C_0(r,t)=\frac{1+r+r^2}{6(1+r)^2(1-t)}.$$
--
--   On the other branch it is the rational expression displayed in the proof of Proposition 3. The coefficient is used in the fixed-quality surplus identity and the sign criterion.
--
--   **Formalization Note** The printed first branch omits $1/(1-t)$. The formula here includes it, as required by integration over $U[t,1]$ and continuity with the printed second branch. The discrepancy is recorded in MODERATION_NOTES.md.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 44 (PDF 45), proof of Proposition 3, C₀ display (corrected first branch)

import Mathlib

namespace AdBlocking.Surplus

/-- The benchmark consumer-surplus multiplier from the proof of Proposition 3.
The first branch includes the normalization factor missing in the printed display. -/
noncomputable def C0 (r t : ℝ) : ℝ :=
  if t ≤ r / (1 + r) then
    (1 + r + r ^ 2) / (6 * (1 + r) ^ 2 * (1 - t))
  else
    ((1 - t) ^ 2 * (1 + r + r ^ 2) +
      3 * ((t - r * (1 - t)) * (1 - r + r ^ 2 * (1 - t)))) /
      (6 * (1 - r * (1 - t)))

end AdBlocking.Surplus


