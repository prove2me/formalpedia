-- Prove2me | Definitions.Def_actuarial_d_annJoint
-- name    : actuarial_d_annJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:34:56.938957+00:00
-- url     : https://prove2.me/theorems/d047fe0e-3c75-4ce0-b052-d9cb3ce38910
-- title:
--   Joint-life annuity
-- statement:
--   Joint-life annuity. Instalments stop when either life has died. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{xy}=\sum_{t=0}^{n-1}d_tb_t S_{xy}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_annValue

namespace ActuarialJointD
noncomputable def annJoint (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := annValue h n p d b both
end ActuarialJointD


