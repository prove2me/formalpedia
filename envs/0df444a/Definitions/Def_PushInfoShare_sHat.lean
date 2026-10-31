-- Prove2me | Definitions.Def_PushInfoShare_sHat
-- name    : PushInfoShare_sHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:24.73212+00:00
-- url     : https://prove2.me/theorems/c7f4011c-e69c-4fa1-93a4-51c1bbe46e3b
-- title:
--   The constant $\hat s=(\sqrt{193}-9)/14$
-- statement:
--   The constant of Proposition 5(b),
--   $$\hat s=\frac{\sqrt{193}-9}{14}\approx0.34946,$$
--   the positive root of $7s^2+9s-4$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(b), p.17

import Mathlib

namespace PushInfoShare

/-- The constant `ŝ = (√193 − 9)/14` of Proposition 5(b), Jain, SSRN:3388957 (PDF of 2021-04-25),
p.17. It is the positive root of `7s² + 9s − 4`. -/
noncomputable def sHat : ℝ :=
  (Real.sqrt 193 - 9) / 14

end PushInfoShare


