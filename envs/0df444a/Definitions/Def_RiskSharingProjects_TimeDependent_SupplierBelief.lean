-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
-- name    : RiskSharingProjects_TimeDependent_SupplierBelief
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:17.704235+00:00
-- url     : https://prove2.me/theorems/5503b33d-51e3-430c-a399-acbbf7e0673a
-- title:
--   The supplier's belief about the manufacturer (Assumption 2)
-- statement:
--   Following Harsanyi, nature draws the manufacturer's cost structure as a random type, and the supplier knows its law (§5). A **supplier belief** is a probability measure $\mu$ on manufacturer types $\theta\in\mathbb R^3$ that gives full mass to the three classes of Assumption 2:
--
--   $$
--   \mu\big(\mathbb R^3\setminus(L\cup M\cup H)\big)=0,
--   $$
--
--   where $L$, $M$, $H$ are the low-, medium- and high-saving types. The class masses are $q^l_0=\mu(L)$, $q^m_0=\mu(M)$, $q^h_0=\mu(H)$, so $q^l_0+q^m_0+q^h_0=1$.
--
--   **Formalization Note** The belief is a general probability measure, not three numbers; a belief putting probabilities $q^l_0,q^m_0,q^h_0$ on three types, one from each class, is a special case.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §5, p. 15; Assumption 2, p. 16

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_lowSavingTypes
import Definitions.Def_RiskSharingProjects_TimeDependent_mediumSavingTypes
import Definitions.Def_RiskSharingProjects_TimeDependent_highSavingTypes

namespace RiskSharingProjects.TimeDependent

/-- **The supplier's belief about the manufacturer's cost structure, Assumption 2.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §5, p. 15: "By Harsanyi (1967), we assume that nature draws a type of cost function for each
firm by the realization of a random variable, and the ex ante probability that the distribution is
public knowledge"; Assumption 2, p. 16: "The supplier holds the following beliefs about the
manufacturer's cost structure s0, p^1_0, and p^2_0: (1) s0 < p^1_0 < p^2_0 with probability q^l_0
…, (2) p^1_0 < s0 < p^2_0 with probability q^m_0 …, and (3) p^1_0 < p^2_0 < s0 with probability
q^h_0 … Note that q^l_0 + q^m_0 + q^h_0 = 1."

`SupplierBelief μ` says that `μ` is a probability measure on manufacturer types
`(s0', p^1_0', p^2_0')` giving full mass to the three classes of Assumption 2.

**Formalization Note.** The belief is a general probability measure (the law of Harsanyi's
random type), not three numbers: q^l_0, q^m_0, q^h_0 are its class masses (`qLow`, `qMedium`,
`qHigh`), and a belief supported on three types with these probabilities is a special case. -/
def SupplierBelief (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧
    μ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ = 0

end RiskSharingProjects.TimeDependent


