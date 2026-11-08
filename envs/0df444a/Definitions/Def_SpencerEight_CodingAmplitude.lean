-- Prove2me | Definitions.Def_SpencerEight_CodingAmplitude
-- name    : SpencerEight_CodingAmplitude
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:39.838573+00:00
-- url     : https://prove2.me/theorems/6ce0f9a4-0661-4c61-92de-09e0358fc4fb
-- title:
--   Coding amplitude
-- statement:
--   A real $s$ is a **coding amplitude** if it satisfies Eq. (59), that is, if there are $a,\delta$ such that $(s,a,\delta)$ satisfies those conditions.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.3, p.71 (PDF p.71); Lemma 8.21, p.84 (PDF p.84)

import Mathlib
import Definitions.Def_SpencerEight_Eq59

namespace SpencerEight

/-- `s` is a coding amplitude: "any amplitude `s` satisfying Eq. (59)" (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.3, p.71 (PDF p.71); Lemma 8.21, p.84 (PDF p.84)). Eq. (59) is a condition on `(s, a, δ)`, so the amplitude is the existential projection. -/
def CodingAmplitude (s : ℝ) : Prop := ∃ a δ : ℝ, Eq59 s a δ

end SpencerEight


