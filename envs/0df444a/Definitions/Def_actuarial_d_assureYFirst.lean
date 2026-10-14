-- Prove2me | Definitions.Def_actuarial_d_assureYFirst
-- name    : actuarial_d_assureYFirst
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:37:50.695041+00:00
-- url     : https://prove2.me/theorems/862b5647-ee5a-4d89-965c-2f93ebec9f84
-- title:
--   Spouse-first contingent assurance
-- statement:
--   Spouse-first contingent assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_{y\prec x}=\sum_{i,j}p_{ij}C_{y\prec x}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_yFirstPath

namespace ActuarialJointD
noncomputable def assureYFirst (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => yFirstPath h d i j)
end ActuarialJointD


