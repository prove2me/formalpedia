-- Prove2me | Definitions.Def_actuarial_commDiscountedLives
-- name    : actuarial_commDiscountedLives
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:05:44.861285+00:00
-- url     : https://prove2.me/theorems/0cbbb1e4-1e04-4903-a01b-60a21845b5d5
-- title:
--   Discounted life table functions: commDiscountedLives
-- statement:
--   Discounted number of lives alive at integer age x. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_x=v^xl_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def commDiscountedLives (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : ℝ := v^x * l x

end ActuarialValuation


