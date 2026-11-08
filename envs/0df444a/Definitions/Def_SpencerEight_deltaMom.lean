-- Prove2me | Definitions.Def_SpencerEight_deltaMom
-- name    : SpencerEight_deltaMom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:58.207665+00:00
-- url     : https://prove2.me/theorems/eb67d10d-3a6b-4188-be5b-81adb9655ab4
-- title:
--   Moment tolerance $\delta_{\mathrm{mom}}$
-- statement:
--   $\delta_{\mathrm{mom}}:=10^{-8}$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.14, p.105 (PDF p.105)

import Mathlib

namespace SpencerEight

/-- `δ_mom := 10⁻⁸` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.14, p.105 (PDF p.105)). -/
noncomputable def deltaMom : ℝ := 1 / 10 ^ 8

end SpencerEight


