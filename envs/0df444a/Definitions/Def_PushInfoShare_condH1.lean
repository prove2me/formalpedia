-- Prove2me | Definitions.Def_PushInfoShare_condH1
-- name    : PushInfoShare_condH1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:22.887093+00:00
-- url     : https://prove2.me/theorems/e92d578c-8246-4c7e-a322-6bf08314d2e5
-- title:
--   Condition $H_1$ for the threshold $\hat\phi_1$ (correction, not in the source)
-- statement:
--   Condition $H_1$ on $(a,\sigma,s)$ is
--   $$a^2(4-s^2)^2(2-s)P(s)>4\sigma s^2(5s+4)^2\bigl(4-s^2(s+2)^2\bigr),\qquad P(s)=14s^4+36s^3+50s^2+48s+32.$$
--   It says that $\lim_{\phi\to\infty}\phi\,(\Pi_i^{P_i}-\Pi_i^N)$ is negative.
--
--   **Formalization Note** This condition is not in the source. It corrects Proposition 5(a), which fails for small $a^2/\sigma$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(a), p.17 (correction of the printed clause)

import Mathlib

namespace PushInfoShare

/-- Condition `H1`, which decides whether the threshold `φ̂₁` of Proposition 5(a) exists:
`a²(4−s²)²(2−s)P(s) > 4σ s²(5s+4)²(4−s²(s+2)²)` with `P(s) = 14s⁴+36s³+50s²+48s+32`.

**Formalization Note.** This condition is not in Jain, SSRN:3388957 (PDF of 2021-04-25). It
corrects Proposition 5(a), p.17: it says that `lim_{φ→∞} φ (Πᵢ^{Pᵢ} − Πᵢᴺ)` is negative. -/
def condH1 (a σ s : ℝ) : Prop :=
  a ^ 2 * (4 - s ^ 2) ^ 2 * (2 - s) * (14 * s ^ 4 + 36 * s ^ 3 + 50 * s ^ 2 + 48 * s + 32) >
    4 * σ * s ^ 2 * (5 * s + 4) ^ 2 * (4 - s ^ 2 * (s + 2) ^ 2)

end PushInfoShare


