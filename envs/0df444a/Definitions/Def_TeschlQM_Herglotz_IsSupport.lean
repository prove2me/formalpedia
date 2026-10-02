-- Prove2me | Definitions.Def_TeschlQM_Herglotz_IsSupport
-- name    : TeschlQM_Herglotz_IsSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:34:39.165324+00:00
-- url     : https://prove2.me/theorems/5642386a-1d79-4573-a196-9d9c3211c559
-- title:
--   Support of a measure: a set whose complement is null
-- statement:
--   A set $A \subseteq \mathbb{R}$ is a **support** for a measure $\mu$ on $\mathbb{R}$ if
--   $$\mu(\mathbb{R} \setminus A) = 0 .$$
--   Supports are not unique; any superset of a support is again a support.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 102, Section 3.2 (after Eq. (3.72)); also p. 99

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99 and p. 102 (after (3.72)): a set `A` is a **support** for the measure `μ` on
`ℝ` if `μ(ℝ \ A) = 0`. -/
def IsSupport (μ : Measure ℝ) (A : Set ℝ) : Prop :=
  μ Aᶜ = 0

end TeschlQM.Herglotz


