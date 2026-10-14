-- Prove2me | Definitions.Def_actuarial_d_onlyX
-- name    : actuarial_d_onlyX
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:31:32.84533+00:00
-- url     : https://prove2.me/theorems/038b0163-ba79-4c3f-b756-ca7c7f48e3bf
-- title:
--   Only the member alive
-- statement:
--   Only the member alive. Member alive with spouse already dead at payment anniversary t. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{x only}}(i,j,t)=I_x(i,t)[1-I_y(j,t)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

namespace ActuarialJointD
noncomputable def onlyX (i j t : ℕ) : ℝ := alive i t * dead j t
end ActuarialJointD


