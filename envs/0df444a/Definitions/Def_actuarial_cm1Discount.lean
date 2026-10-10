-- Prove2me | Definitions.Def_actuarial_cm1Discount
-- name    : actuarial_cm1Discount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:26:51.754977+00:00
-- url     : https://prove2.me/theorems/484cceff-b89e-46b1-83cf-0f23905095a5
-- title:
--   Interest rate algebra: cm1Discount
-- statement:
--   The corresponding discounted unit payment due in n integer years; a valid positive accumulation rate requires i greater than minus one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   v_n(i)=1/(1+i)^n
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Accum

namespace ActuarialValuation

noncomputable def cm1Discount (i : ℝ) (n : ℕ) : ℝ := 1 / cm1Accum i n

end ActuarialValuation


