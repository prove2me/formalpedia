-- Prove2me | Definitions.Def_SpencerEight_sPlus
-- name    : SpencerEight_sPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:51.871198+00:00
-- url     : https://prove2.me/theorems/6ed678dc-54b5-47ac-b14b-2736302f59b4
-- title:
--   Refined coding amplitude $s_+$
-- statement:
--   $s_+:=0.674489750196$, an exact rational, used for the final signing.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.42, p.104 (PDF p.104)

import Mathlib

namespace SpencerEight

/-- The refined coding amplitude `s₊ := 0.674489750196` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.42, p.104 (PDF p.104)). An exact rational. -/
noncomputable def sPlus : ℝ := 0.674489750196

end SpencerEight


