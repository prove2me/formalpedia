-- Prove2me | Definitions.Def_actuarial_d_pureJoint
-- name    : actuarial_d_pureJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:39:16.614949+00:00
-- url     : https://prove2.me/theorems/4391e790-73e3-4db1-867d-741e3faf6663
-- title:
--   Joint pure endowment
-- statement:
--   Joint pure endowment. Maturity amount if both lives are alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_{xy}(t)=d_tS_{xy}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pxy

namespace ActuarialJointD
noncomputable def pureJoint (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := d t * pxy h p t
end ActuarialJointD


