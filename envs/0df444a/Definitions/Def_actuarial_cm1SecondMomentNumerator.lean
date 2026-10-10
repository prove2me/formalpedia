-- Prove2me | Definitions.Def_actuarial_cm1SecondMomentNumerator
-- name    : actuarial_cm1SecondMomentNumerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:37:02.539918+00:00
-- url     : https://prove2.me/theorems/2785aca8-bc02-4684-948b-7075bb179e6c
-- title:
--   Bond pricing and immunisation: cm1SecondMomentNumerator
-- statement:
--   Positive discounted convexity-weighted aggregate relevant to the second derivative of liability value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_{\rm num}=\sum_{k<n}(k+1)(k+2)c_kv^{k+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1SecondMomentNumerator (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, ((k + 1 : ℕ) * (k + 2 : ℕ)) * c k * cm1Discount i (k+1)

end ActuarialValuation


