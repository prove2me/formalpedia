-- Prove2me | Definitions.Def_actuarial_commSurvivorSum
-- name    : actuarial_commSurvivorSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:06:26.04504+00:00
-- url     : https://prove2.me/theorems/79b34a62-8ed1-48a4-a7ed-283b0b6519c2
-- title:
--   Finite commutation functions: commSurvivorSum
-- statement:
--   Finite commutation sum for an n-payment annuity due. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N_{x:n}=\sum_{k<n}D_{x+k}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

namespace ActuarialValuation

noncomputable def commSurvivorSum (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, commDiscountedLives l v (x+k)

end ActuarialValuation


