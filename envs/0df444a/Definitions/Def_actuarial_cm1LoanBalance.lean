-- Prove2me | Definitions.Def_actuarial_cm1LoanBalance
-- name    : actuarial_cm1LoanBalance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:35:44.537629+00:00
-- url     : https://prove2.me/theorems/7342a216-5f1e-4460-86e5-a69a7c835643
-- title:
--   General cashflows and loan balances: cm1LoanBalance
-- statement:
--   Prospective outstanding balance of remaining loan repayments at valuation time t. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_t=\sum_{k+1>t}P_kv^{k+1-t}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

noncomputable def cm1LoanBalance (payment : ℕ → ℝ) (n t : ℕ) (i : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, if t < k+1 then payment k * cm1Discount i (k+1-t) else 0

end ActuarialValuation


