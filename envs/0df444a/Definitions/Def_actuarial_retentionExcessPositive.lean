-- Prove2me | Definitions.Def_actuarial_retentionExcessPositive
-- name    : actuarial_retentionExcessPositive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:44:22.299215+00:00
-- url     : https://prove2.me/theorems/ef8cdd92-3219-45b7-9775-ecd21590618e
-- title:
--   Positive excess of loss above real-valued deductible
-- statement:
--   This is an original derived actuarial definition, based on the stop-loss premium as expectation of positive excess. The indemnity for a nonnegative severity above a real retention equals its positive excess and is zero below the attachment. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   (x-d)_+=\max(x-d,0)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration actuarial_retentionExcessPositive is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def retentionExcessPositive (x d : ℝ) : ℝ :=
  max (x - d) 0

end ActuarialValuation


