-- Prove2me | Definitions.Def_ParamSDPTraj_OuterSemicontAt
-- name    : ParamSDPTraj_OuterSemicontAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:31.380547+00:00
-- url     : https://prove2.me/theorems/277439d5-970c-40fc-b970-7e7607aab589
-- title:
--   Outer semicontinuity at a point
-- statement:
--   A set-valued map $F$ is **outer semicontinuous** at $\hat t\in T$ if
--
--   $$\limsup_{t\to\hat t}F(t)\subseteq F(\hat t).$$
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.12, p.8

import Mathlib
import Definitions.Def_ParamSDPTraj_outerLimit

namespace ParamSDPTraj

/-- **Outer semicontinuity at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.12, p.8: "F is outer semi-continuous at t̂ ∈ T if lim sup_{t→t̂} F(t) ⊆ F(t̂)". -/
def OuterSemicontAt {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E) (that : ℝ) :
    Prop :=
  outerLimit T F that ⊆ F that

end ParamSDPTraj


