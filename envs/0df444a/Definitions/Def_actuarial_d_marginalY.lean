-- Prove2me | Definitions.Def_actuarial_d_marginalY
-- name    : actuarial_d_marginalY
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:27.328568+00:00
-- url     : https://prove2.me/theorems/2a0afef3-6052-4149-bd40-74c1dbe70208
-- title:
--   Spouse death-year marginal
-- statement:
--   Spouse death-year marginal. Marginal death-year mass from the same original joint probability table. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   v_j=\sum_{i=0}^{h}p_{ij}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def marginalY (h : ℕ) (p : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range (h+1), p i j
end ActuarialJointD


