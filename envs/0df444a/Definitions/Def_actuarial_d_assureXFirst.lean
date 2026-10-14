-- Prove2me | Definitions.Def_actuarial_d_assureXFirst
-- name    : actuarial_d_assureXFirst
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:37:37.718906+00:00
-- url     : https://prove2.me/theorems/1a43ebcb-f48c-4284-a31a-03d754c19c6c
-- title:
--   Member-first contingent assurance
-- statement:
--   Member-first contingent assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_{x\prec y}=\sum_{i,j}p_{ij}C_{x\prec y}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_xFirstPath

namespace ActuarialJointD
noncomputable def assureXFirst (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => xFirstPath h d i j)
end ActuarialJointD


