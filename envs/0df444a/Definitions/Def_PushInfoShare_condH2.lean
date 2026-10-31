-- Prove2me | Definitions.Def_PushInfoShare_condH2
-- name    : PushInfoShare_condH2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:24.843052+00:00
-- url     : https://prove2.me/theorems/702d232e-3c0b-429f-b74c-ad74874dfcbe
-- title:
--   Condition $H_2$ for the threshold $\hat\phi_2$ (correction, not in the source)
-- statement:
--   Condition $H_2$ on $(a,\sigma,s)$ is
--   $$a^2(4-s^2)^3(7s^2+9s-4)>\sigma s\,(4-s^4-3s^3-4s^2)(5s+4)^2.$$
--   It says that $\lim_{\phi\to\infty}\phi\,(\Pi_i^F-\Pi_i^{P_{3-i}})$ is negative. The factor $7s^2+9s-4$ is the source of the printed constant $\hat s$.
--
--   **Formalization Note** This condition is not in the source. It corrects Proposition 5(b), whose threshold fails to exist for some $s>\hat s$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(b), p.17 (correction of the printed clause)

import Mathlib

namespace PushInfoShare

/-- Condition `H2`, which decides whether the threshold `φ̂₂` of Proposition 5(b) exists when
`s > ŝ`: `a²(4−s²)³(7s²+9s−4) > σ s(4−s⁴−3s³−4s²)(5s+4)²`.

**Formalization Note.** This condition is not in Jain, SSRN:3388957 (PDF of 2021-04-25). It
corrects Proposition 5(b), p.17: it says that `lim_{φ→∞} φ (Πᵢᶠ − Πᵢ^{P₃₋ᵢ})` is negative. The
factor `7s²+9s−4` is what makes the printed constant `ŝ` appear. -/
def condH2 (a σ s : ℝ) : Prop :=
  a ^ 2 * (4 - s ^ 2) ^ 3 * (7 * s ^ 2 + 9 * s - 4) >
    σ * s * (4 - s ^ 4 - 3 * s ^ 3 - 4 * s ^ 2) * (5 * s + 4) ^ 2

end PushInfoShare


