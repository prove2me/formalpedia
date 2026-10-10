-- Prove2me | Definitions.Def_actuarial_orderAggregateMean
-- name    : actuarial_orderAggregateMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:23:49.983557+00:00
-- url     : https://prove2.me/theorems/88ae8594-d4d7-4a21-bae4-25636908178e
-- title:
--   Bounded aggregate loss expectation
-- statement:
--   The finite aggregate claims mean uses the claim amount at each integer index as its payment and multiplies it by its probability mass. Comparing mean claims is necessary when interpreting stop-loss order as mean-preserving convex order.
--
--   **Mathematical statement**
--
--   $$
--   \mu_w=\sum_{s=0}^{B}sw_s
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration actuarial_orderAggregateMean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def orderAggregateMean (w : ℕ → ℝ) (bound : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1), (s : ℝ) * w s

end ActuarialValuation


