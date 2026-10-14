-- Prove2me | Definitions.Def_actuarial_d_assureSecond
-- name    : actuarial_d_assureSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:37:25.456431+00:00
-- url     : https://prove2.me/theorems/ec058238-417c-4bbd-bdfc-73bab3820033
-- title:
--   Second-death assurance
-- statement:
--   Second-death assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_2=\sum_{i,j}p_{ij}C_2(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_secondPath

namespace ActuarialJointD
noncomputable def assureSecond (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => secondPath h d i j)
end ActuarialJointD


