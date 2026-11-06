-- Prove2me | Definitions.Def_TiltedCvx_IsProper
-- name    : TiltedCvx_IsProper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:53.766195+00:00
-- url     : https://prove2.me/theorems/1dcadeac-ce85-4471-ab64-7903ab496eb3
-- title:
--   Proper extended-real-valued function
-- statement:
--   A function $f:\mathbb R^d\to\overline{\mathbb R}$ is **proper** if its domain is nonempty and it never takes the value $-\infty$:
--
--   $$
--   \operatorname{dom}(f)\neq\emptyset\quad\text{and}\quad f(x)>-\infty\ \text{ for all } x .
--   $$
--
--   This is the standing convention of the paper for minimization; all function classes of the mission consist of proper functions.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.10

import Mathlib
import Definitions.Def_TiltedCvx_effDom

namespace TiltedCvx

/-- **Proper function.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3, p.10:
`f : ℝ^d → ℝ̄` is proper if `dom(f) ≠ ∅` and `f > −∞`. -/
def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (effDom f).Nonempty ∧ ∀ x, f x ≠ ⊥

end TiltedCvx


