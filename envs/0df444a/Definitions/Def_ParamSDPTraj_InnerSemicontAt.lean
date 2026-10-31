-- Prove2me | Definitions.Def_ParamSDPTraj_InnerSemicontAt
-- name    : ParamSDPTraj_InnerSemicontAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:43.894141+00:00
-- url     : https://prove2.me/theorems/74f03fbe-2372-4c94-a0b1-fddec52e4f06
-- title:
--   Inner semicontinuity at a point
-- statement:
--   A set-valued map $F$ is **inner semicontinuous** at $\hat t\in T$ if
--
--   $$\liminf_{t\to\hat t}F(t)\supseteq F(\hat t).$$
--
--   A *loss of inner semicontinuity* at $t$ means that this inclusion fails at $t$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.12, p.8

import Mathlib
import Definitions.Def_ParamSDPTraj_innerLimit

namespace ParamSDPTraj

/-- **Inner semicontinuity at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.12, p.8: "F is inner semi-continuous at t̂ ∈ T if lim inf_{t→t̂} F(t) ⊇ F(t̂)". -/
def InnerSemicontAt {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E) (that : ℝ) :
    Prop :=
  F that ⊆ innerLimit T F that

end ParamSDPTraj


