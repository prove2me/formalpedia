-- Prove2me | Definitions.Def_ParamSDPTraj_PKContinuousAt
-- name    : ParamSDPTraj_PKContinuousAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:33.584952+00:00
-- url     : https://prove2.me/theorems/7fa5ae7e-a98b-4d9a-b11a-3179cdf09997
-- title:
--   Painlevé–Kuratowski continuity at a point
-- statement:
--   A set-valued map $F$ is **Painlevé–Kuratowski continuous** at $\hat t$ if it is both outer and inner semicontinuous at $\hat t$. From Remark 2.13 on, the paper calls this simply *continuity*.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.12 and Remark 2.13, p.8

import Mathlib
import Definitions.Def_ParamSDPTraj_OuterSemicontAt
import Definitions.Def_ParamSDPTraj_InnerSemicontAt

namespace ParamSDPTraj

/-- **Painlevé–Kuratowski continuity at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.12, p.8: "F is Painlevé-Kuratowski continuous at t̂ if it is both outer and
inner semi-continuous at t̂". By Remark 2.13, p.8, this is what the paper calls "continuous". -/
def PKContinuousAt {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E) (that : ℝ) :
    Prop :=
  OuterSemicontAt T F that ∧ InnerSemicontAt T F that

end ParamSDPTraj


