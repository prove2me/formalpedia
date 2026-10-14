-- Prove2me | Definitions.Def_actuarial_d_both
-- name    : actuarial_d_both
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:31:10.808646+00:00
-- url     : https://prove2.me/theorems/5bcdbc14-29c2-4b84-9cc1-2615b51384e7
-- title:
--   Both lives alive
-- statement:
--   Both lives alive. Joint-life occupation indicator at payment anniversary t. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{both}}(i,j,t)=I_x(i,t)I_y(j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive

namespace ActuarialJointD
noncomputable def both (i j t : ℕ) : ℝ := alive i t * alive j t
end ActuarialJointD


