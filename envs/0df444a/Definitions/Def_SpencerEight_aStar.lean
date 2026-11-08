-- Prove2me | Definitions.Def_SpencerEight_aStar
-- name    : SpencerEight_aStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:51.753278+00:00
-- url     : https://prove2.me/theorems/c928e5f3-9ece-46fa-8a08-5b8a86159026
-- title:
--   Original density height $a_\star$
-- statement:
--   $a_\star:=0.635$, an exact rational. Together with $b_\star:=(1-2s_\star a_\star)/s_\star^2$ it fixes the original density of $Z$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)

import Mathlib

namespace SpencerEight

/-- The original density height `a⋆ := 0.635` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)). An exact rational. -/
noncomputable def aStar : ℝ := 0.635

end SpencerEight


