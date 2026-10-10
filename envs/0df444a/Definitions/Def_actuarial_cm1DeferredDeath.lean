-- Prove2me | Definitions.Def_actuarial_cm1DeferredDeath
-- name    : actuarial_cm1DeferredDeath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:49:53.785979+00:00
-- url     : https://prove2.me/theorems/bef0d858-65ee-48c4-be47-ac8945c05d19
-- title:
--   Life tables and survival composition: cm1DeferredDeath
-- statement:
--   The probability of surviving deferral k and then dying during the next n-year period. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_{k|n}q_x={}_kp_x\,{}_nq_{x+k}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 5. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
import Definitions.Def_actuarial_cm1LifeMortality

namespace ActuarialValuation

noncomputable def cm1DeferredDeath (l : ℕ → ℝ) (x k n : ℕ) : ℝ :=
  cm1LifeSurvival l x k * cm1LifeMortality l (x+k) n

end ActuarialValuation


