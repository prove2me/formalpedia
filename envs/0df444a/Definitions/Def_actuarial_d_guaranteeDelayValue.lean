-- Prove2me | Definitions.Def_actuarial_d_guaranteeDelayValue
-- name    : actuarial_d_guaranteeDelayValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:51:08.229432+00:00
-- url     : https://prove2.me/theorems/dc0156d1-e3f0-46c7-a9f3-f71342dbf140
-- title:
--   Guarantee-then-reversion EPV
-- statement:
--   Guarantee-then-reversion EPV. One joint-law expected value of the explicitly designated guaranteed and spouse streams. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{delay}}=\mathbb E_p[Z_{\text{delay}}]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_guaranteeDelayPath

namespace ActuarialJointD
noncomputable def guaranteeDelayValue (h n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : ℝ := expect h p (fun i j => guaranteeDelayPath n g d b rho i j)
end ActuarialJointD


