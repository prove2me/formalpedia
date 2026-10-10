-- Prove2me | Definitions.Def_actuarial_cm1EffectiveDiscount
-- name    : actuarial_cm1EffectiveDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:30:05.555339+00:00
-- url     : https://prove2.me/theorems/80b5b2df-5f21-44d5-b6ab-247d832eec31
-- title:
--   Interest rate algebra: cm1EffectiveDiscount
-- statement:
--   The effective discount rate relates the one-year interest rate to its time-zero unit discount. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d=i/(1+i)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialValuation

noncomputable def cm1EffectiveDiscount (i : ℝ) : ℝ := i / (1+i)

end ActuarialValuation


