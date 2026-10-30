-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_qLow
-- name    : RiskSharingProjects_TimeDependent_qLow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:46.433697+00:00
-- url     : https://prove2.me/theorems/9b6ef6c7-f980-44e6-b184-cca1f4e0b6dc
-- title:
--   The belief probability $q^l_0$
-- statement:
--   For a supplier belief $\mu$, $q^l_0=\mu(L)$ is the probability the supplier assigns to the manufacturer's type lying in the class $L$ of Assumption 2(1), as a real number.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(1), p. 16

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_lowSavingTypes

namespace RiskSharingProjects.TimeDependent

/-- **The belief probability `q^l_0` of Assumption 2(1).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16. `qLow μ` is the mass the supplier's belief `μ` puts on
`lowSavingTypes`, as a real number.

**Formalization Note.** For a probability measure the mass is finite, so `ENNReal.toReal` loses
nothing. -/
noncomputable def qLow (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) : ℝ :=
  (μ lowSavingTypes).toReal

end RiskSharingProjects.TimeDependent


