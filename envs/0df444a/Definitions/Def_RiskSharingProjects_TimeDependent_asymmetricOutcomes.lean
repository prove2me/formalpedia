-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_asymmetricOutcomes
-- name    : RiskSharingProjects_TimeDependent_asymmetricOutcomes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:55.967975+00:00
-- url     : https://prove2.me/theorems/9e150057-7681-400e-abe9-7ba05fd799ca
-- title:
--   Equilibrium outcomes under information asymmetry
-- statement:
--   Under information asymmetry the supplier chooses an equilibrium decision under its belief, and the actual manufacturer, with true cost structure $(s_0,p^1_0,p^2_0)$, observes it and best-responds. The set of **equilibrium outcomes** is
--
--   $$
--   \mathcal O^{\mathrm{asym}}=\{(a_1,a_0):\ a_1\in\mathcal A^\mu,\ a_0\in\mathrm{BR}_0(a_1)\}.
--   $$
--
--   Like the SPNE outcomes under symmetry, it keeps every tie.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §5, p. 16; proof of Theorem 6, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerBestResponses
import Definitions.Def_RiskSharingProjects_TimeDependent_asymmetricSupplierChoices

namespace RiskSharingProjects.TimeDependent

/-- **Equilibrium outcomes under information asymmetry.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §5, p. 16: "After observing the suppliers' actions, the manufacturer takes its action, and
thus, effectively enjoys an information advantage over the suppliers"; proof of Theorem 6,
Appendix p. 5 (PDF 37).

`asymmetricOutcomes μ s1 p11 p21 s0 p10 p20` is the set of action pairs `(a1, a0)` in which `a1`
is an equilibrium decision of the supplier under its belief `μ` and `a0` is a best response of
the actual manufacturer, of type `(s0, p^1_0, p^2_0)`, to `a1`.

**Formalization Note.** Set-valued, as `symmetricSPNEOutcomes`: every tie is kept. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def asymmetricOutcomes (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (s1 p11 p21 s0 p10 p20 : ℝ) :
    Set (Action × Action) :=
  {o | o.1 ∈ asymmetricSupplierChoices μ s1 p11 p21 ∧
    o.2 ∈ manufacturerBestResponses s0 p10 p20 o.1}

end RiskSharingProjects.TimeDependent


