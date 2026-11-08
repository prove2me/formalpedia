-- Prove2me | Definitions.Def_SpencerEight_gaussG
-- name    : SpencerEight_gaussG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:54.262649+00:00
-- url     : https://prove2.me/theorems/7ff70583-544c-4fd4-96d0-3a9360981a9c
-- title:
--   Density $g=F'$
-- statement:
--   $g(x):=F'(x)=\sqrt{2/\pi}\,e^{-x^2/2}$, used in Eq. (59).
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), proof of Lemma 8.2, pp.69–70 (PDF pp.69–70)

import Mathlib

namespace SpencerEight

/-- `g(x) := F′(x) = √(2/π) e^{−x²/2}` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), proof of Lemma 8.2, pp.69–70 (PDF pp.69–70)). -/
noncomputable def gaussG (x : ℝ) : ℝ := Real.sqrt (2 / Real.pi) * Real.exp (-x ^ 2 / 2)

end SpencerEight


