-- Prove2me | Definitions.Def_actuarial_d_guaranteeMember
-- name    : actuarial_d_guaranteeMember
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:52.048977+00:00
-- url     : https://prove2.me/theorems/9258826a-da65-4110-8bf5-ce6fe62cd57a
-- title:
--   Guaranteed member-payment indicator
-- statement:
--   Guaranteed member-payment indicator. Early guaranteed instalments continue irrespective of member survival, with later payments on survival. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   G_g(i,t)=\begin{cases}1&t<g\\I_x(i,t)&t\geq g\end{cases}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive

namespace ActuarialJointD
noncomputable def guaranteeMember (g i t : ℕ) : ℝ := if t < g then (1 : ℝ) else alive i t
end ActuarialJointD


