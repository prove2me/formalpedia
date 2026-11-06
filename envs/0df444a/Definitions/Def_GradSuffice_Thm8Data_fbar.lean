-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_fbar
-- name    : GradSuffice_Thm8Data_fbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:30.346403+00:00
-- url     : https://prove2.me/theorems/b54a27c3-aa27-484c-85fe-f95fbc5c39c8
-- title:
--   The averaged hard function $\bar f=\mathbb E_Z[f]$
-- statement:
--   The hard function of Theorem 8 is $\bar f(w):=\mathbb E_Z[f(w)]$, the expectation over all auxiliary noise variables, with the sampled branches held fixed.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_f
import Definitions.Def_GradSuffice_Thm8Data_noiseLaw

namespace GradSuffice

/-- **The averaged hard function `f̄ := E_Z[f]`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19: "The expectation in `f̄` is
taken over all the auxiliary noise variables appearing in the construction, but not over the
sampled branches". -/
noncomputable def Thm8Data.fbar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (w : X) : ℝ :=
  ∫ Z, c.f Z w ∂c.noiseLaw

end GradSuffice


