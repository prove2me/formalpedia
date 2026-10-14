-- Prove2me | Definitions.Def_actuarial_d_guaranteeOverlapValue
-- name    : actuarial_d_guaranteeOverlapValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:51:40.456934+00:00
-- url     : https://prove2.me/theorems/a424dc05-11a6-45ce-a373-add263b38cba
-- title:
--   Expected overlapping annuity instalments
-- statement:
--   Expected overlapping annuity instalments. The cashflow difference produced by paying a spouse during the guarantee window. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{overlap}}=\mathbb E_p[Z_{\text{overlap}}]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_guaranteeOverlapPath

namespace ActuarialJointD
noncomputable def guaranteeOverlapValue (h n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : ℝ := expect h p (fun i j => guaranteeOverlapPath n g d b i j)
end ActuarialJointD


