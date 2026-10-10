-- Prove2me | Definitions.Def_actuarial_retentionStopLossPremium
-- name    : actuarial_retentionStopLossPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:44:36.773155+00:00
-- url     : https://prove2.me/theorems/89e8c817-72c2-4dfa-b767-949d068ba5ef
-- title:
--   Weighted finite stop-loss net premium at a retention
-- statement:
--   This is an original derived actuarial definition, based on the stop-loss premium as expectation of positive excess. The pure stop-loss premium is the finite probability-weighted expectation of the positive claim amount above retention d. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \Pi(d)=\sum_{s=0}^{B}w_s(X_s-d)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration actuarial_retentionStopLossPremium is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive

namespace ActuarialValuation

noncomputable def retentionStopLossPremium
  (w X : ℕ → ℝ) (B : ℕ) (d : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (B + 1),
    w s * retentionExcessPositive (X s) d

end ActuarialValuation


