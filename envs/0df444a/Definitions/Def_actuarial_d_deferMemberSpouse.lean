-- Prove2me | Definitions.Def_actuarial_d_deferMemberSpouse
-- name    : actuarial_d_deferMemberSpouse
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:47:05.429948+00:00
-- url     : https://prove2.me/theorems/bbe3d571-7ec5-4043-9667-82b5b3ff582d
-- title:
--   Deferred member-and-spouse continuation
-- statement:
--   Deferred member-and-spouse continuation. Pays the member before death and rho times the amount to the eligible surviving spouse. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{a,n;\rho}=a_{x;a,n}+\rho a_{y\mid x;a,n}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_deferValue

namespace ActuarialJointD
noncomputable def deferMemberSpouse (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : ℝ := deferValue h a n p d b (fun i j t => alive i t + rho * onlyY i j t)
end ActuarialJointD


