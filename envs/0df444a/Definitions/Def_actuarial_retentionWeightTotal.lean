-- Prove2me | Definitions.Def_actuarial_retentionWeightTotal
-- name    : actuarial_retentionWeightTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:44:43.836974+00:00
-- url     : https://prove2.me/theorems/af2580fb-8e9d-44c0-8b68-ed94db399d61
-- title:
--   Total scenario weight of finite severity model
-- statement:
--   This is an original derived actuarial definition, based on the stop-loss premium as expectation of positive excess. The total mass of the finite scenarios is one for a probability distribution, but arbitrary nonnegative finite mass is also allowed in intermediate inequalities. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   W=\sum_{s=0}^{B}w_s
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration actuarial_retentionWeightTotal is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def retentionWeightTotal (w : ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (B + 1), w s

end ActuarialValuation


