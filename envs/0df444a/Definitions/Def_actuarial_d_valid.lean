-- Prove2me | Definitions.Def_actuarial_d_valid
-- name    : actuarial_d_valid
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:30:36.932016+00:00
-- url     : https://prove2.me/theorems/bd630584-12e6-47df-b270-aef694503595
-- title:
--   Coherent finite joint law
-- statement:
--   Coherent finite joint law. Nonnegative joint cell probabilities whose total mass is one. No independence is imposed. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{ij}\geq0,\quad\sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mass

namespace ActuarialJointD
noncomputable def valid (h : ℕ) (p : ℕ → ℕ → ℝ) : Prop := (∀ i ∈ Finset.range (h+1), ∀ j ∈ Finset.range (h+1), 0 ≤ p i j) ∧ mass h p = 1
end ActuarialJointD


