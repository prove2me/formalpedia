-- Prove2me | Definitions.Def_SpencerEight_LH
-- name    : SpencerEight_LH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:18.426804+00:00
-- url     : https://prove2.me/theorems/2219ec85-5a37-4cf7-89d8-05270f0ad396
-- title:
--   Logarithmic profile $L_H$
-- statement:
--   For $H>1$,
--   $$L_H(x):=\frac{H\log(1+x)-\log(1+Hx)}{(H-1)x},\qquad L_H(0):=0.$$
--   This is the profile by which Lemma 8.15 pays the determinant factor.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, p.79 (PDF p.79)

import Mathlib

namespace SpencerEight

/-- The logarithmic profile (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, p.79 (PDF p.79)): `L_H(x) := (H log(1 + x) − log(1 + Hx))/((H − 1)x)`, `L_H(0) := 0`.

**Formalization Note** The value at zero is explicit. Every use has `H > 1` and `x ≥ 0`, so both logarithms have positive arguments. -/
noncomputable def LH (H x : ℝ) : ℝ :=
  if x = 0 then 0 else (H * Real.log (1 + x) - Real.log (1 + H * x)) / ((H - 1) * x)

end SpencerEight


