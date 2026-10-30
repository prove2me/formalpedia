-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_AsymmetryShortensDuration
-- name    : RiskSharingProjects_TimeDependent_AsymmetryShortensDuration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:31.050878+00:00
-- url     : https://prove2.me/theorems/ef92c6a3-853e-41ab-a9c2-ade93ddb7a2d
-- title:
--   Information asymmetry shortens the project's duration
-- statement:
--   **Information asymmetry shortens the project's duration relative to information symmetry** when every equilibrium outcome under asymmetry has strictly fewer periods of project delay than every SPNE outcome under symmetry:
--
--   $$
--   \mathrm{delay}(o)<\mathrm{delay}(o')\quad\text{for all } o\in\mathcal O^{\mathrm{asym}},\ o'\in\mathcal O^{\mathrm{sym}}.
--   $$
--
--   When both equilibria are unique this is the comparison of the two durations made in Theorem 6.
--
--   **Formalization Note** At indifference points the equilibria are sets of outcomes; the definition then asks every asymmetric outcome to be strictly shorter than every symmetric one.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Theorem 6, p. 17

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_projectDelay
import Definitions.Def_RiskSharingProjects_TimeDependent_symmetricSPNEOutcomes
import Definitions.Def_RiskSharingProjects_TimeDependent_asymmetricOutcomes

namespace RiskSharingProjects.TimeDependent

/-- **Information asymmetry shortens the project's duration relative to information symmetry.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Theorem 6, p. 17: "information asymmetry shortens the project's duration relative to
information symmetry".

`AsymmetryShortensDuration μ s1 p11 p21 s0 p10 p20` says that every equilibrium outcome under
asymmetry (`asymmetricOutcomes`) has a strictly smaller project delay than every SPNE outcome
under symmetry (`symmetricSPNEOutcomes`).

**Formalization Note.** When both equilibria are unique this is the paper's comparison of the two
durations. At indifference points the equilibria are sets and "shortens" requires every
asymmetric outcome to be strictly shorter than every symmetric one. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def AsymmetryShortensDuration (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ))
    (s1 p11 p21 s0 p10 p20 : ℝ) : Prop :=
  ∀ o ∈ asymmetricOutcomes μ s1 p11 p21 s0 p10 p20,
    ∀ o' ∈ symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20,
      projectDelay o.1 o.2 < projectDelay o'.1 o'.2

end RiskSharingProjects.TimeDependent


