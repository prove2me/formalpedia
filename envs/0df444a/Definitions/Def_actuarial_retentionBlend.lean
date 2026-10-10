-- Prove2me | Definitions.Def_actuarial_retentionBlend
-- name    : actuarial_retentionBlend
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:45:15.578174+00:00
-- url     : https://prove2.me/theorems/c45b26bb-0968-4438-be3f-0a340dd97650
-- title:
--   Convex combination of two retentions
-- statement:
--   This is an original derived actuarial definition, based on the stop-loss premium as expectation of positive excess. A scenario-independent interpolation between retentions is in their closed interval when the blending weight belongs to the unit interval. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   d_\theta=(1-\theta)a+\theta b
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 409 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: actuarial stop-loss transform and decreasing convex premium as retention varies, supporting source https://www.researchgate.net/publication/4958878_The_Concept_of_Comonotonicity_in_Actuarial_Science_And_Finance_Theory. The Lean declaration actuarial_retentionBlend is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def retentionBlend (a b θ : ℝ) : ℝ :=
  (1 - θ) * a + θ * b

end ActuarialValuation


