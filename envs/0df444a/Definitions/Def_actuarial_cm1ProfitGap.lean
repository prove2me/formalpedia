-- Prove2me | Definitions.Def_actuarial_cm1ProfitGap
-- name    : actuarial_cm1ProfitGap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:36:27.394605+00:00
-- url     : https://prove2.me/theorems/cf8b5470-efc5-421e-9d8d-34c692b1f1c2
-- title:
--   Bond pricing and immunisation: cm1ProfitGap
-- statement:
--   Difference between asset and liability present values under one common flat effective yield. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S(i)=V_A(i)-V_L(i)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV

namespace ActuarialValuation

noncomputable def cm1ProfitGap (assets liabilities : ℕ → ℝ) (n : ℕ) (i : ℝ) : ℝ :=
  cm1CashflowPV assets n i - cm1CashflowPV liabilities n i

end ActuarialValuation


