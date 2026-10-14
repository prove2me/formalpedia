-- Prove2me | Definitions.Def_actuarial_d_pxy
-- name    : actuarial_d_pxy
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:33:13.817698+00:00
-- url     : https://prove2.me/theorems/d9de1dba-921a-4192-994e-2d4ade2ed0c7
-- title:
--   Joint survival
-- statement:
--   Joint survival. Both lives alive. Dependence is retained through the joint mass function. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   S_{xy}(t)=\sum_{i,j}p_{ij}I_x(i,t)I_y(j,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_expect

namespace ActuarialJointD
noncomputable def pxy (h : ℕ) (p : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := expect h p (fun i j => both i j t)
end ActuarialJointD


