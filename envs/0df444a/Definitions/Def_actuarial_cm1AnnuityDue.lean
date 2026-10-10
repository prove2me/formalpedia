-- Prove2me | Definitions.Def_actuarial_cm1AnnuityDue
-- name    : actuarial_cm1AnnuityDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:30:33.938058+00:00
-- url     : https://prove2.me/theorems/8f8d7521-daa4-4d60-9fb6-bb235d1db646
-- title:
--   Annuity certain identities: cm1AnnuityDue
-- statement:
--   Present value of n unit payments in advance at times zero through n minus one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_n=\sum_{k<n}v^k
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1AnnuityDue (i : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, cm1Discount i k

end ActuarialValuation


