-- Prove2me | Definitions.Def_actuarial_cm1IncreasingImmediate
-- name    : actuarial_cm1IncreasingImmediate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:32:12.860488+00:00
-- url     : https://prove2.me/theorems/4859ec1f-9a1a-4173-932a-05d6476b300b
-- title:
--   Annuity certain identities: cm1IncreasingImmediate
-- statement:
--   Arithmetically increasing cashflows starting at one unit and increasing by one each payment year. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (Ia)_n=\sum_{k=1}^n kv^k
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1IncreasingImmediate (i : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℕ) * cm1Discount i (k+1)

end ActuarialValuation


