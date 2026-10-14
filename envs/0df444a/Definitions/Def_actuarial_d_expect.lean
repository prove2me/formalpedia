-- Prove2me | Definitions.Def_actuarial_d_expect
-- name    : actuarial_d_expect
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:32:36.067691+00:00
-- url     : https://prove2.me/theorems/92475f9c-9714-4b2a-8935-d9e934c513bf
-- title:
--   Joint-law expectation
-- statement:
--   Joint-law expectation. Expected present value of a realised function of both death-year states. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E_p[g]=\sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}g(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def expect (h : ℕ) (p : ℕ → ℕ → ℝ) (g : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1), p i j * g i j
end ActuarialJointD


