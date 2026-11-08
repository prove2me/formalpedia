-- Prove2me | Definitions.Def_SpencerEight_codingB
-- name    : SpencerEight_codingB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:38.843093+00:00
-- url     : https://prove2.me/theorems/4e430c60-3a97-46df-8e51-c373e48e006c
-- title:
--   Normalizing parameter $b=(1-2sa)/s^2$
-- statement:
--   The parameter $b:=(1-2sa)/s^2$ of the coding density, chosen so that $2sa+s^2b=1$.
--
--   **Formalization Note** Every use has $s>0$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69); Eq. (59), p.70 (PDF p.70)

import Mathlib

namespace SpencerEight

/-- The normalizing parameter `b := (1 − 2sa)/s²` of the coding density (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69), and Eq. (59), p.70 (PDF p.70)).

**Formalization Note** Every use has `s > 0`, so the division is genuine. -/
noncomputable def codingB (s a : ℝ) : ℝ := (1 - 2 * s * a) / s ^ 2

end SpencerEight


