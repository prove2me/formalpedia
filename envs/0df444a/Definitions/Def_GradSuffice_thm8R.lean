-- Prove2me | Definitions.Def_GradSuffice_thm8R
-- name    : GradSuffice_thm8R
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:24.239608+00:00
-- url     : https://prove2.me/theorems/04c598d7-4018-470c-9ca2-e99e93ed6e80
-- title:
--   The scale $r=\theta/256$ of Theorem 8
-- statement:
--   For a margin $\theta$, the hard instance of Theorem 8 uses the scale $r:=\theta/256$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8, p.18

import Mathlib

namespace GradSuffice

/-- **The scale `r := θ/256`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8, p.18. -/
noncomputable def thm8R (θ : ℝ) : ℝ := θ / 256

end GradSuffice


