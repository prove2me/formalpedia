-- Prove2me | Definitions.Def_actuarial_orderAggregateMass
-- name    : actuarial_orderAggregateMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:23:59.715612+00:00
-- url     : https://prove2.me/theorems/093db49a-0f1c-435c-9195-a01183c5f87a
-- title:
--   Aggregate probability within a finite loss bound
-- statement:
--   The sum of all coefficients on the finite aggregate-loss support is the bounded probability mass, whose value is one for a normalised distribution. An explicit mass operator makes the mean-preserving spread's total-mass conservation separately checkable.
--
--   **Mathematical statement**
--
--   $$
--   M_w=\sum_{s=0}^{B}w_s
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration actuarial_orderAggregateMass is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def orderAggregateMass (w : ℕ → ℝ) (bound : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1), w s

end ActuarialValuation


