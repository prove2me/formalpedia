-- Prove2me | Definitions.Def_HighDimStat_UniformLaws_IsUniformlyBounded
-- name    : HighDimStat_UniformLaws_IsUniformlyBounded
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:38.573502+00:00
-- url     : https://prove2.me/theorems/d44187a0-764d-43e7-beac-a5928b1e539a
-- title:
--   A b-uniformly bounded function class
-- statement:
--   A function class $F = \{f_j, j\in\iota\}$ is $b$-**uniformly bounded** if $\|f\|_\infty\le b$
--   for all $f\in F$. This is the regularity condition Theorem 4.10's sub-Gaussian tail bound
--   requires.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 105 (PDF p. 125)

import Mathlib

namespace HighDimStat.UniformLaws

/-- A function class `F = {f_j, j ∈ ι}` is `b`-**uniformly bounded**, Wainwright,
*High-Dimensional Statistics* (2019), p. 105: `‖f‖∞ ≤ b` for all `f ∈ F`. -/
def IsUniformlyBounded {D ι : Type*} (f : ι → D → ℝ) (b : ℝ) : Prop :=
  ∀ j : ι, ∀ x : D, |f j x| ≤ b

end HighDimStat.UniformLaws


