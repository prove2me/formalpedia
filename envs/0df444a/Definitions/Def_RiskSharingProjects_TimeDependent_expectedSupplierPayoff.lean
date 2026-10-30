-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_expectedSupplierPayoff
-- name    : RiskSharingProjects_TimeDependent_expectedSupplierPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:28.710121+00:00
-- url     : https://prove2.me/theorems/68eadab0-9c48-40c3-8ff0-cc932e66a392
-- title:
--   The supplier's expected payoff under its belief
-- statement:
--   Under information asymmetry the supplier does not know the manufacturer's type. If it plays $a_1$, its **expected payoff** under the belief $\mu$ is
--
--   $$
--   U_1^\mu(a_1)=\int u_1\big(a_1,r_\theta(a_1)\big)\,d\mu(\theta).
--   $$
--
--   **Formalization Note** The integrand takes at most four values and is measurable, hence integrable for a probability measure; the integral is the expectation.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 5, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_supplierPayoff
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerResponse

namespace RiskSharingProjects.TimeDependent

/-- **The supplier's expected payoff under its belief.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 5, Appendix p. 5 (PDF 37): "In summary, the supplier's expected payoff
under her beliefs is −p^1_1(q^m_0 + q^h_0)."

`expectedSupplierPayoff μ s1 p11 p21 a1` is the integral over manufacturer types `θ ∼ μ` of the
supplier's payoff when it plays `a1` and the manufacturer of type `θ` responds with
`manufacturerResponse θ a1`.

**Formalization Note.** The integrand takes at most four values and is measurable, so it is
integrable under a probability measure; the Bochner integral is the expectation (no junk value
`0`). Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
noncomputable def expectedSupplierPayoff (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ))
    (s1 p11 p21 : ℝ) (a1 : Action) : ℝ :=
  ∫ θ, supplierPayoff s1 p11 p21 a1 (manufacturerResponse θ a1) ∂μ

end RiskSharingProjects.TimeDependent


