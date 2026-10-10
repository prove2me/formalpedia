-- Prove2me | Definitions.Def_actuarial_cm1MacaulayDuration
-- name    : actuarial_cm1MacaulayDuration
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:37:53.794985+00:00
-- url     : https://prove2.me/theorems/21d2622a-d181-48d1-b7e4-383904e57bb5
-- title:
--   Bond pricing and immunisation: cm1MacaulayDuration
-- statement:
--   Macaulay duration of a nonzero-valued dated positive cashflow stream. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D= D_{\rm num}/V_c
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1DurationNumerator

namespace ActuarialValuation

noncomputable def cm1MacaulayDuration (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : ℝ :=
  cm1DurationNumerator c n i / cm1CashflowPV c n i

end ActuarialValuation


