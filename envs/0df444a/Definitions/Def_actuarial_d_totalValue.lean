-- Prove2me | Definitions.Def_actuarial_d_totalValue
-- name    : actuarial_d_totalValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:40:14.681841+00:00
-- url     : https://prove2.me/theorems/2e3acb61-5e89-4027-a602-be912dff4ae6
-- title:
--   State-occupation valuation
-- statement:
--   State-occupation valuation. Expected value obtained by averaging actual joint-life cashflows state by state. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{total}}=\sum_{i,j}p_{ij}Z_{\text{total}}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_totalPath

namespace ActuarialJointD
noncomputable def totalValue (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : ℝ := expect h p (fun i j => totalPath h n d b rho f s fx fy ft i j)
end ActuarialJointD


