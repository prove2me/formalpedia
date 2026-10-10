-- Prove2me | Definitions.Def_actuarial_commDeathSum
-- name    : actuarial_commDeathSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:07:52.232903+00:00
-- url     : https://prove2.me/theorems/7fc2bd63-20ce-4715-9a59-bd08e0cfc9e0
-- title:
--   Finite commutation functions: commDeathSum
-- statement:
--   Finite commutation sum for an n-year term assurance payable at year end. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{x:n}=\sum_{k<n}C_{x+k}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedDeaths

namespace ActuarialValuation

noncomputable def commDeathSum (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, commDiscountedDeaths l v (x+k)

end ActuarialValuation


