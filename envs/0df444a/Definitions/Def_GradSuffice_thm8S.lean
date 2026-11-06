-- Prove2me | Definitions.Def_GradSuffice_thm8S
-- name    : GradSuffice_thm8S
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:26.428728+00:00
-- url     : https://prove2.me/theorems/1a245992-ac4b-48bf-a4eb-71bb89a3b6ef
-- title:
--   The scale $s=r^2/8$ of Theorem 8
-- statement:
--   For a margin $\theta$, the hard instance of Theorem 8 uses the scale $s:=r^2/8$, where $r=\theta/256$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8, p.18

import Mathlib
import Definitions.Def_GradSuffice_thm8R

namespace GradSuffice

/-- **The scale `s := r²/8`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8, p.18. -/
noncomputable def thm8S (θ : ℝ) : ℝ := thm8R θ ^ 2 / 8

end GradSuffice


