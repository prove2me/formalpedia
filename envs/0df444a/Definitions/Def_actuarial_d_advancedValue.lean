-- Prove2me | Definitions.Def_actuarial_d_advancedValue
-- name    : actuarial_d_advancedValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:53:24.89483+00:00
-- url     : https://prove2.me/theorems/efe632c3-4374-412c-9a0e-cb73b2018bc2
-- title:
--   Advanced contract expectation from joint states
-- statement:
--   Advanced contract expectation from joint states. Valuation by direct summation of realised discounted contractual payments over the true joint death-time law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{advanced}}=\sum_{i,j}p_{ij}Z_{\text{advanced}}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_advancedPath

namespace ActuarialJointD
noncomputable def advancedValue (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : ℝ := expect h p (fun i j => advancedPath h a n g d b rho f s fx fy ft i j)
end ActuarialJointD


