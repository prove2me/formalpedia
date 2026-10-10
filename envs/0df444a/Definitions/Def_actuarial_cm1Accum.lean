-- Prove2me | Definitions.Def_actuarial_cm1Accum
-- name    : actuarial_cm1Accum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:26:37.063001+00:00
-- url     : https://prove2.me/theorems/c47b500d-5b9a-4dec-adc4-9b901ee8d40b
-- title:
--   Interest rate algebra: cm1Accum
-- statement:
--   The effective annual investment accumulation factor at n integer years, using a common annual rate i. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_n(i)=(1+i)^n
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialValuation

noncomputable def cm1Accum (i : ℝ) (n : ℕ) : ℝ := (1 + i) ^ n

end ActuarialValuation


