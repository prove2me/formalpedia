-- Prove2me | Definitions.Def_actuarial_cm1AnnuityImmediate
-- name    : actuarial_cm1AnnuityImmediate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:31:53.390163+00:00
-- url     : https://prove2.me/theorems/43a81299-8539-467a-ac23-32aca2c90bf8
-- title:
--   Annuity certain identities: cm1AnnuityImmediate
-- statement:
--   Present value of n unit payments in arrears, from time one to time n. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_n=\sum_{k=1}^n v^k
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1AnnuityImmediate (i : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, cm1Discount i (k+1)

end ActuarialValuation


