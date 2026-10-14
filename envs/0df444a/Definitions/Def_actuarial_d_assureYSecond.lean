-- Prove2me | Definitions.Def_actuarial_d_assureYSecond
-- name    : actuarial_d_assureYSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:38:28.069129+00:00
-- url     : https://prove2.me/theorems/295f59bd-4d05-4adb-88ae-2f78bb5d9bb6
-- title:
--   Spouse-second contingent assurance
-- statement:
--   Spouse-second contingent assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_{y\succ x}=\sum_{i,j}p_{ij}C_{y\succ x}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_ySecondPath

namespace ActuarialJointD
noncomputable def assureYSecond (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => ySecondPath h d i j)
end ActuarialJointD


