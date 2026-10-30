-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_highSavingTypes
-- name    : RiskSharingProjects_TimeDependent_highSavingTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:48.587834+00:00
-- url     : https://prove2.me/theorems/9b8bf46f-10f4-4e2e-99c8-59d822968696
-- title:
--   High-saving manufacturer types, Assumption 2(3)
-- statement:
--   A manufacturer **type** is a triple $\theta=(s_0',p^{1\prime}_0,p^{2\prime}_0)\in\mathbb R^3$: the saving from delay and the shares of the first- and second-period delay penalties.
--
--   The **high-saving** types are those with
--
--   $$
--   p^{1\prime}_0<p^{2\prime}_0<s_0' .
--   $$
--
--   The supplier believes the manufacturer is of this kind with probability $q^h_0$.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(3), p. 16

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **High-saving manufacturer types, Assumption 2(3).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16: "(3) p^1_0 < p^2_0 < s0 with probability q^h_0 (superscript "h"
indicates high saving.)".

A manufacturer type is a triple `θ = (s0', p^1_0', p^2_0') : ℝ × ℝ × ℝ`: its saving from delay and
its shares of the first- and second-period delay penalties (`θ.1`, `θ.2.1`, `θ.2.2`). -/
def highSavingTypes : Set (ℝ × ℝ × ℝ) :=
  {θ | θ.2.1 < θ.2.2 ∧ θ.2.2 < θ.1}

end RiskSharingProjects.TimeDependent


