-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_lowSavingTypes
-- name    : RiskSharingProjects_TimeDependent_lowSavingTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:17.903986+00:00
-- url     : https://prove2.me/theorems/9d5dc385-31c5-4800-9a89-31ad2e2d706e
-- title:
--   Low-saving manufacturer types, Assumption 2(1)
-- statement:
--   A manufacturer **type** is a triple $\theta=(s_0',p^{1\prime}_0,p^{2\prime}_0)\in\mathbb R^3$: the saving from delay and the shares of the first- and second-period delay penalties.
--
--   The **low-saving** types are those with
--
--   $$
--   s_0'<p^{1\prime}_0<p^{2\prime}_0 .
--   $$
--
--   The supplier believes the manufacturer is of this kind with probability $q^l_0$.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(1), p. 16

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **Low-saving manufacturer types, Assumption 2(1).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16: "(1) s0 < p^1_0 < p^2_0 with probability q^l_0 (superscript "l"
indicates low saving relative to p^1_0 and p^2_0)".

A manufacturer type is a triple `θ = (s0', p^1_0', p^2_0') : ℝ × ℝ × ℝ`: its saving from delay and
its shares of the first- and second-period delay penalties (`θ.1`, `θ.2.1`, `θ.2.2`). -/
def lowSavingTypes : Set (ℝ × ℝ × ℝ) :=
  {θ | θ.1 < θ.2.1 ∧ θ.2.1 < θ.2.2}

end RiskSharingProjects.TimeDependent


