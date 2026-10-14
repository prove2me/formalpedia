-- Prove2me | Definitions.Def_actuarial_d_guaranteeDelayPath
-- name    : actuarial_d_guaranteeDelayPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:50:20.683576+00:00
-- url     : https://prove2.me/theorems/a9bab8c3-6eda-48a0-9736-14779691aa44
-- title:
--   Guarantee-then-reversion realised pension
-- statement:
--   Guarantee-then-reversion realised pension. Member-guarantee payments can continue to a designated beneficiary; spouse fraction starts after guarantee. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{delay}}=\sum_t d_tb_t[G_g(i,t)+\rho R_g(i,j,t)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_delayedSpouse

namespace ActuarialJointD
noncomputable def guaranteeDelayPath (n g : ℕ) (d b : ℕ → ℝ) (rho : ℝ) (i j : ℕ) : ℝ := annPath n d b (fun t => guaranteeMember g i t + rho * delayedSpouse g i j t)
end ActuarialJointD


