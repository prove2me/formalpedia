-- Prove2me | Definitions.Def_actuarial_d_dead
-- name    : actuarial_d_dead
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:30:59.106973+00:00
-- url     : https://prove2.me/theorems/3e32bc4f-dd1f-4c81-82fb-72fa5dfd0878
-- title:
--   Dead by the anniversary
-- statement:
--   Dead by the anniversary. Complement to the live state after the death-year boundary. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   D_x(i,t)=1-I_x(i,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive

namespace ActuarialJointD
noncomputable def dead (i t : ℕ) : ℝ := 1 - alive i t
end ActuarialJointD


