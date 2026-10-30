-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_asymmetricSupplierChoices
-- name    : RiskSharingProjects_TimeDependent_asymmetricSupplierChoices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:26.138337+00:00
-- url     : https://prove2.me/theorems/b3a1d71e-4071-430e-a86c-9f96263fd375
-- title:
--   The supplier's equilibrium decisions under information asymmetry
-- statement:
--   The supplier's **equilibrium decisions** under information asymmetry are the actions that maximize its expected payoff:
--
--   $$
--   \mathcal A^\mu=\{a_1:\ U_1^\mu(b)\le U_1^\mu(a_1)\ \text{for all } b\}.
--   $$
--
--   They depend only on the belief $\mu$ and the supplier's own $s_1,p^1_1,p^2_1$, never on the manufacturer's true cost structure. At indifference both actions are equilibrium decisions.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §5, p. 16; Theorem 5, p. 17

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_expectedSupplierPayoff

namespace RiskSharingProjects.TimeDependent

/-- **The supplier's equilibrium decisions under information asymmetry.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §5, p. 16: "In single supplier cases, we characterize the supplier's equilibrium decisions,
contingent upon its beliefs"; Theorem 5, p. 17.

`asymmetricSupplierChoices μ s1 p11 p21` is the set of supplier actions maximizing
`expectedSupplierPayoff μ s1 p11 p21`.

**Formalization Note.** The supplier does not know the manufacturer's true `(s0, p^1_0, p^2_0)`,
so the set depends only on its belief `μ` and its own `s1, p^1_1, p^2_1`. At indifference both
actions are in the set. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def asymmetricSupplierChoices (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (s1 p11 p21 : ℝ) :
    Set Action :=
  {a1 | ∀ b, expectedSupplierPayoff μ s1 p11 p21 b ≤ expectedSupplierPayoff μ s1 p11 p21 a1}

end RiskSharingProjects.TimeDependent


