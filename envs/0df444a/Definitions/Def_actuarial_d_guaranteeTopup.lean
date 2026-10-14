-- Prove2me | Definitions.Def_actuarial_d_guaranteeTopup
-- name    : actuarial_d_guaranteeTopup
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:51:50.22198+00:00
-- url     : https://prove2.me/theorems/29903d66-3a26-4e24-90b9-31a8e4bbce6c
-- title:
--   Additional payment under member guarantee
-- statement:
--   Additional payment under member guarantee. Guaranteed-only amount after member death and before the guarantee expires. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   U_g(i,t)=I_{\{t<g\}}[1-I_x(i,t)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive

namespace ActuarialJointD
noncomputable def guaranteeTopup (g i t : ℕ) : ℝ := if t < g then (1 : ℝ) - alive i t else 0
end ActuarialJointD


