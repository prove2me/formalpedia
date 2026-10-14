-- Prove2me | Definitions.Def_actuarial_d_mass
-- name    : actuarial_d_mass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:30:18.580863+00:00
-- url     : https://prove2.me/theorems/b00a8f74-66dd-46a8-aaf3-1b977b2355cc
-- title:
--   Joint probability mass
-- statement:
--   Joint probability mass. Total probability assigned to the two death-year states, including right-censored survival at the horizon. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   \sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def mass (h : ℕ) (p : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (h+1), ∑ j ∈ Finset.range (h+1), p i j
end ActuarialJointD


