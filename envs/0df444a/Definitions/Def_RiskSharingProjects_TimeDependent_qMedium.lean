-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_qMedium
-- name    : RiskSharingProjects_TimeDependent_qMedium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:20:14.143212+00:00
-- url     : https://prove2.me/theorems/5506b1ac-2692-4236-9b7b-4b3c71539051
-- title:
--   The belief probability $q^m_0$
-- statement:
--   For a supplier belief $\mu$, $q^m_0=\mu(M)$ is the probability the supplier assigns to the manufacturer's type lying in the class $M$ of Assumption 2(2), as a real number.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(2), p. 16

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_mediumSavingTypes

namespace RiskSharingProjects.TimeDependent

/-- **The belief probability `q^m_0` of Assumption 2(2).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16. `qMedium μ` is the mass the supplier's belief `μ` puts on
`mediumSavingTypes`, as a real number.

**Formalization Note.** For a probability measure the mass is finite, so `ENNReal.toReal` loses
nothing. -/
noncomputable def qMedium (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) : ℝ :=
  (μ mediumSavingTypes).toReal

end RiskSharingProjects.TimeDependent


