-- Prove2me | Definitions.Def_actuarial_d_annMemberSpouse
-- name    : actuarial_d_annMemberSpouse
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:35:45.374463+00:00
-- url     : https://prove2.me/theorems/ee006281-da64-4f53-b7f0-7f851e21b1f6
-- title:
--   Member-and-spouse annuity
-- statement:
--   Member-and-spouse annuity. Member gets a full instalment while alive; spouse gets fraction rho only after member death. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{x;\rho y}=a_x+\rho a_{y\mid x}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annMemberSpouse (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : ℝ := annValue h n p d b (fun i j t => alive i t + rho * onlyY i j t)
end ActuarialJointD


