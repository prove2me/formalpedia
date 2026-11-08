-- Prove2me | Definitions.Def_SpencerEight_aPlus
-- name    : SpencerEight_aPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:52.37472+00:00
-- url     : https://prove2.me/theorems/6b036d5a-d20f-42b4-bf86-92e039087717
-- title:
--   Refined density height
-- statement:
--   $a:=0.635553145368$, an exact rational, the density height that goes with $s_+$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.42, p.104 (PDF p.104)

import Mathlib

namespace SpencerEight

/-- The refined density height `a := 0.635553145368` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.42, p.104 (PDF p.104)). An exact rational. -/
noncomputable def aPlus : ℝ := 0.635553145368

end SpencerEight


