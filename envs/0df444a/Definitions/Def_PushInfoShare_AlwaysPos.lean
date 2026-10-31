-- Prove2me | Definitions.Def_PushInfoShare_AlwaysPos
-- name    : PushInfoShare_AlwaysPos
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:20.807997+00:00
-- url     : https://prove2.me/theorems/b4430e43-47a5-4a2c-8b75-b433ba4fc197
-- title:
--   Positive for every $\phi\ge0$
-- statement:
--   A function $g$ is positive for every $\phi\ge0$: the "for all values of $\phi$" of Proposition 5(b).
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(b), p.17

import Mathlib

namespace PushInfoShare

/-- `g > 0` at every `φ ≥ 0`, the "for all values of φ" of Proposition 5(b), Jain, SSRN:3388957
(PDF of 2021-04-25), p.17. -/
def AlwaysPos (g : ℝ → ℝ) : Prop :=
  ∀ φ, 0 ≤ φ → 0 < g φ

end PushInfoShare


