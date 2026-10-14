-- Prove2me | Definitions.Def_actuarial_d_assureXSecond
-- name    : actuarial_d_assureXSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:38:15.63388+00:00
-- url     : https://prove2.me/theorems/ee32099a-8724-4307-ad10-e983cbf36ada
-- title:
--   Member-second contingent assurance
-- statement:
--   Member-second contingent assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_{x\succ y}=\sum_{i,j}p_{ij}C_{x\succ y}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_xSecondPath

namespace ActuarialJointD
noncomputable def assureXSecond (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => xSecondPath h d i j)
end ActuarialJointD


