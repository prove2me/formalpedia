-- Prove2me | Definitions.Def_SpencerEight_Eq59
-- name    : SpencerEight_Eq59
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:49.197443+00:00
-- url     : https://prove2.me/theorems/3d9e0f99-7d79-4b46-aef1-cd93075245fb
-- title:
--   The sufficient conditions Eq. (59)
-- statement:
--   The conditions on $(s,a,\delta)$, with $b:=(1-2sa)/s^2$ and $0<\delta<s<1$:
--   $$b>0,\quad a>bs,\quad a+bs>g(0),\quad g(s)>a>g(s+\delta),$$
--   $$\tfrac12-F(s)>\delta(g(s)-a)>0,\quad 1-F(5s/2)>bs^2/2,\quad 1-F(3s)>bs^2/8.$$
--   The source verifies them at $(0.67448,\,0.635,\,0.01)$ and at $(0.674489750196,\,0.635553145368,\,10^{-12})$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Eq. (59), p.70 (PDF p.70)

import Mathlib
import Definitions.Def_SpencerEight_codingB
import Definitions.Def_SpencerEight_gaussF
import Definitions.Def_SpencerEight_gaussG

namespace SpencerEight

/-- The sufficient conditions Eq. (59) (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.70 (PDF p.70)) on `(s, a, δ)`, with `b := (1 − 2sa)/s²` and `0 < δ < s < 1`: `b > 0`, `a > bs`, `a + bs > g(0)`, `g(s) > a > g(s + δ)`, `1/2 − F(s) > δ(g(s) − a) > 0`, `1 − F(5s/2) > bs²/2`, `1 − F(3s) > bs²/8`. -/
def Eq59 (s a δ : ℝ) : Prop :=
  0 < δ ∧ δ < s ∧ s < 1 ∧
  0 < codingB s a ∧
  codingB s a * s < a ∧
  gaussG 0 < a + codingB s a * s ∧
  a < gaussG s ∧
  gaussG (s + δ) < a ∧
  δ * (gaussG s - a) < 1 / 2 - gaussF s ∧
  0 < δ * (gaussG s - a) ∧
  codingB s a * s ^ 2 / 2 < 1 - gaussF (5 * s / 2) ∧
  codingB s a * s ^ 2 / 8 < 1 - gaussF (3 * s)

end SpencerEight


