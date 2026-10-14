-- Prove2me | Definitions.Def_actuarial_d_guaranteeParallelPath
-- name    : actuarial_d_guaranteeParallelPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:50:38.084363+00:00
-- url     : https://prove2.me/theorems/91ddf4c8-9e19-4ccb-9a61-fc841219f1e0
-- title:
--   Guarantee plus parallel reversion
-- statement:
--   Guarantee plus parallel reversion. A separate spouse pension may commence on member death and overlap guaranteed payments. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{parallel}}=\sum_t d_tb_t[G_g(i,t)+\rho I_{\text{y only}}(i,j,t)]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_guaranteeMember

namespace ActuarialJointD
noncomputable def guaranteeParallelPath (n g : ℕ) (d b : ℕ → ℝ) (rho : ℝ) (i j : ℕ) : ℝ := annPath n d b (fun t => guaranteeMember g i t + rho * onlyY i j t)
end ActuarialJointD


