-- Prove2me | Definitions.Def_actuarial_cm1DurationNumerator
-- name    : actuarial_cm1DurationNumerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:36:45.932975+00:00
-- url     : https://prove2.me/theorems/de8c8286-ffc3-42c2-bf7c-89f13ab49fd9
-- title:
--   Bond pricing and immunisation: cm1DurationNumerator
-- statement:
--   Discounted time-weighted sum of cashflows, preceding normalized Macaulay duration. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{\rm num}=\sum_{k<n}(k+1)c_kv^{k+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1DurationNumerator (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k + 1 : ℕ) * c k * cm1Discount i (k+1)

end ActuarialValuation


