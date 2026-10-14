-- Prove2me | Definitions.Def_actuarial_d_marginalX
-- name    : actuarial_d_marginalX
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:18.852419+00:00
-- url     : https://prove2.me/theorems/45be248e-c062-4b65-99aa-b4c23c8c5be5
-- title:
--   Member death-year marginal
-- statement:
--   Member death-year marginal. Summing across every spouse death-year outcome preserves dependence information. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   u_i=\sum_{j=0}^{h}p_{ij}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def marginalX (h : ℕ) (p : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (h+1), p i j
end ActuarialJointD


