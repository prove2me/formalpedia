-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_qHigh
-- name    : RiskSharingProjects_TimeDependent_qHigh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:20:45.691984+00:00
-- url     : https://prove2.me/theorems/a3c27dbd-76f8-4786-8129-ec9558ef2d8e
-- title:
--   The belief probability $q^h_0$
-- statement:
--   For a supplier belief $\mu$, $q^h_0=\mu(H)$ is the probability the supplier assigns to the manufacturer's type lying in the class $H$ of Assumption 2(3), as a real number.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Assumption 2(3), p. 16

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_highSavingTypes

namespace RiskSharingProjects.TimeDependent

/-- **The belief probability `q^h_0` of Assumption 2(3).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Assumption 2, p. 16. `qHigh μ` is the mass the supplier's belief `μ` puts on
`highSavingTypes`, as a real number.

**Formalization Note.** For a probability measure the mass is finite, so `ENNReal.toReal` loses
nothing. -/
noncomputable def qHigh (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) : ℝ :=
  (μ highSavingTypes).toReal

end RiskSharingProjects.TimeDependent


