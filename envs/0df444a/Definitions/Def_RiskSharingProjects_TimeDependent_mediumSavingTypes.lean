-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_mediumSavingTypes
-- name    : RiskSharingProjects_TimeDependent_mediumSavingTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:34.41234+00:00
-- url     : https://prove2.me/theorems/617021cb-560c-492c-a811-100f441e6751
-- title:
--   Medium-saving manufacturer types, Assumption 2(2)
-- statement:
--   A manufacturer **type** is a triple $\theta=(s_0',p^{1\prime}_0,p^{2\prime}_0)\in\mathbb R^3$: the saving from delay and the shares of the first- and second-period delay penalties.
--
--   The **medium-saving** types are those with
--
--   $$
--   p^{1\prime}_0<s_0'<p^{2\prime}_0 .
--   $$
--
--   The supplier believes the manufacturer is of this kind with probability $q^m_0$.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(2), p. 16

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **Medium-saving manufacturer types, Assumption 2(2).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16: "(2) p^1_0 < s0 < p^2_0 with probability q^m_0 (superscript "m"
indicates medium saving)".

A manufacturer type is a triple `θ = (s0', p^1_0', p^2_0') : ℝ × ℝ × ℝ`: its saving from delay and
its shares of the first- and second-period delay penalties (`θ.1`, `θ.2.1`, `θ.2.2`). -/
def mediumSavingTypes : Set (ℝ × ℝ × ℝ) :=
  {θ | θ.2.1 < θ.1 ∧ θ.1 < θ.2.2}

end RiskSharingProjects.TimeDependent


