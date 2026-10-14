-- Prove2me | Definitions.Def_actuarial_d_guaranteeParallelValue
-- name    : actuarial_d_guaranteeParallelValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:51:25.545502+00:00
-- url     : https://prove2.me/theorems/973cca85-7233-46b9-88b1-0ba3164b2987
-- title:
--   Guarantee with parallel reversion EPV
-- statement:
--   Guarantee with parallel reversion EPV. One joint-law expected value of the explicitly designated guaranteed and spouse streams. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{parallel}}=\mathbb E_p[Z_{\text{parallel}}]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_guaranteeParallelPath

namespace ActuarialJointD
noncomputable def guaranteeParallelValue (h n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : ℝ := expect h p (fun i j => guaranteeParallelPath n g d b rho i j)
end ActuarialJointD


