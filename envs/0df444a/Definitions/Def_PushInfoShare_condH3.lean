-- Prove2me | Definitions.Def_PushInfoShare_condH3
-- name    : PushInfoShare_condH3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:28.045595+00:00
-- url     : https://prove2.me/theorems/4e59814b-e306-416f-a830-82a5d1efc8db
-- title:
--   Condition $H_3$ for the threshold $\hat\phi_3$ (correction, not in the source)
-- statement:
--   Condition $H_3$ on $(a,\sigma,s)$ is
--   $$a^2(2-s)^3(1+s)^2>2\sigma s^2(1-2s-s^2).$$
--   It says that $\lim_{\phi\to\infty}\phi\,(\Pi_i^F-\Pi_i^N)$ is negative.
--
--   **Formalization Note** This condition is not in the source. It corrects Proposition 5(c), which fails for small $a^2/\sigma$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(c), p.17 (correction of the printed clause)

import Mathlib

namespace PushInfoShare

/-- Condition `H3`, which decides whether the threshold `φ̂₃` of Proposition 5(c) exists:
`a²(2−s)³(1+s)² > 2σ s²(1−2s−s²)`.

**Formalization Note.** This condition is not in Jain, SSRN:3388957 (PDF of 2021-04-25). It
corrects Proposition 5(c), p.17: it says that `lim_{φ→∞} φ (Πᵢᶠ − Πᵢᴺ)` is negative. -/
def condH3 (a σ s : ℝ) : Prop :=
  a ^ 2 * (2 - s) ^ 3 * (1 + s) ^ 2 > 2 * σ * s ^ 2 * (1 - 2 * s - s ^ 2)

end PushInfoShare


