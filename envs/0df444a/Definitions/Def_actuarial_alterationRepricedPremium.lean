-- Prove2me | Definitions.Def_actuarial_alterationRepricedPremium
-- name    : actuarial_alterationRepricedPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:04:37.299194+00:00
-- url     : https://prove2.me/theorems/a9c72114-5a13-4b52-8ad8-8d172885f85f
-- title:
--   Prospective reserve and premium difference: alterationRepricedPremium
-- statement:
--   Premium for remaining insurance benefits if the policy is repriced as a new contract at the valuation age. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_s=B/a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def alterationRepricedPremium (futureBenefits premiumAnnuity : ℝ) : ℝ := futureBenefits / premiumAnnuity

end ActuarialValuation


