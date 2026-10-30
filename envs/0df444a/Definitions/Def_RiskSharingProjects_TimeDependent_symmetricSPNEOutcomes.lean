-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_symmetricSPNEOutcomes
-- name    : RiskSharingProjects_TimeDependent_symmetricSPNEOutcomes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:04.256175+00:00
-- url     : https://prove2.me/theorems/781b969b-048a-4de5-802f-bbac5a5b3c32
-- title:
--   Outcomes of the subgame perfect equilibria under information symmetry
-- statement:
--   Under information symmetry the supplier moves first, and the manufacturer, having observed the supplier's action, moves second (§4). A pure-strategy **subgame perfect Nash equilibrium (SPNE)** consists of a manufacturer strategy $\sigma$ (an action after each supplier action) with $\sigma(a)\in\mathrm{BR}_0(a)$ for both $a$, and a supplier action $a_1$ maximizing $b\mapsto u_1(b,\sigma(b))$. The set of **SPNE outcomes** is
--
--   $$
--   \mathcal O^{\mathrm{sym}}=\{(a_1,\sigma(a_1)):\ (a_1,\sigma)\ \text{is an SPNE}\}.
--   $$
--
--   **Formalization Note** When the SPNE is not unique (at indifference points) every SPNE outcome belongs to the set; the paper's selection of a Pareto or strong equilibrium (p. 10) is not imposed.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §4, p. 10; Theorem 2, p. 12

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_supplierPayoff
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerBestResponses

namespace RiskSharingProjects.TimeDependent

/-- **Outcomes of the subgame perfect Nash equilibria under information symmetry.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §4, p. 10: "Suppliers first choose the task duration and carry out their tasks. Upon
observing the suppliers' actions and their task durations, the manufacturer then chooses its task
duration. … We derived the subgame perfect Nash equilibrium (SPNE)"; Theorem 2, p. 12.

`symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20` is the set of action pairs `(a1, a0)` reached by a
pure-strategy SPNE of the two-stage game with complete information: a manufacturer strategy
`σ : Action → Action` best-responding after each supplier action, and a supplier action `a1`
maximizing `supplierPayoff s1 p11 p21 b (σ b)` over `b`, with `a0 = σ a1`.

**Formalization Note.** Equilibria are set-valued: when the SPNE is not unique (at indifference
points) every SPNE outcome is in the set; the paper's selection of a Pareto or strong equilibrium
(p. 10) is not imposed. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def symmetricSPNEOutcomes (s1 p11 p21 s0 p10 p20 : ℝ) : Set (Action × Action) :=
  {o | ∃ σ : Action → Action, (∀ a, σ a ∈ manufacturerBestResponses s0 p10 p20 a) ∧
    (∀ b, supplierPayoff s1 p11 p21 b (σ b) ≤ supplierPayoff s1 p11 p21 o.1 (σ o.1)) ∧
    o.2 = σ o.1}

end RiskSharingProjects.TimeDependent


