-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_Condition2
-- name    : RiskSharingProjects_TimeDependent_Condition2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:44.096985+00:00
-- url     : https://prove2.me/theorems/80f84d4c-5325-4907-9cad-6caf291597b0
-- title:
--   Condition 2: global optimum and monotonicity
-- statement:
--   Write $p^1=p^1_1+p^1_0$ and $p^2=p^2_1+p^2_0$ for the total penalties of the first and second period of project delay. **Condition 2** is
--
--   1. (Global Optimum) $s_1<p^1$ and $s_0<p^1$;
--   2. (Monotonicity) $p^1<p^2$, $p^1_1<p^2_1$ and $p^1_0<p^2_0$.
--
--   The first part makes $[K,K]$ optimal for a single firm doing all the work; the second reflects a convex, increasing project cost.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Condition 2, p. 12

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **Condition 2 (global optimum and monotonicity).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §4.1, p. 12: "Condition 2 (1) Global Optimum: s1 < p^1, s0 < p^1. (2) Monotonicity:
p^1 < p^2, p^1_1 < p^2_1, p^1_0 < p^2_0", where "p^1_1 + p^1_0 = p^1 and p^2_1 + p^2_0 = p^2".

`Condition2 s1 s0 p11 p21 p10 p20` is
`(s1 < p11 + p10 ∧ s0 < p11 + p10) ∧ (p11 + p10 < p21 + p20 ∧ p11 < p21 ∧ p10 < p20)`.

**Formalization Note.** The totals p^1, p^2 are written as the sums of the firms' shares. Part (2)
is Assumption 1(b)'s "non-decreasing penalty per period" (p. 10) in the strict form in which
Condition 2 states it. The argument order `s1 s0 p11 p21 p10 p20` is used everywhere. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def Condition2 (s1 s0 p11 p21 p10 p20 : ℝ) : Prop :=
  (s1 < p11 + p10 ∧ s0 < p11 + p10) ∧ (p11 + p10 < p21 + p20 ∧ p11 < p21 ∧ p10 < p20)

end RiskSharingProjects.TimeDependent


