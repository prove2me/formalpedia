-- Prove2me | Definitions.Def_actuarial_cm1LifeSurvival
-- name    : actuarial_cm1LifeSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:48:56.155139+00:00
-- url     : https://prove2.me/theorems/95979edd-09a0-4406-b6f6-4365ed746d78
-- title:
--   Life tables and survival composition: cm1LifeSurvival
-- statement:
--   A life-table cohort survival probability defined as the ratio of two positive starting and future life counts. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_np_x=l_{x+n}/l_x
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 5. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def cm1LifeSurvival (l : ℕ → ℝ) (x n : ℕ) : ℝ := l (x+n) / l x

end ActuarialValuation


