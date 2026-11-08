-- Prove2me | Definitions.Def_SpencerEight_sStar
-- name    : SpencerEight_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:55.409195+00:00
-- url     : https://prove2.me/theorems/56c07704-7c9d-4952-aecb-a01c45cdfdc5
-- title:
--   Original coding amplitude $s_\star$
-- statement:
--   $s_\star:=0.67448$, an exact rational. It is the amplitude of all constructions unless the refined one is specified.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)

import Mathlib

namespace SpencerEight

/-- The original coding amplitude `s⋆ := 0.67448` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)). An exact rational (Section 8: "Every terminating decimal below denotes an exact rational number"). -/
noncomputable def sStar : ℝ := 0.67448

end SpencerEight


