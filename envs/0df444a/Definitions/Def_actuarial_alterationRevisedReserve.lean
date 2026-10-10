-- Prove2me | Definitions.Def_actuarial_alterationRevisedReserve
-- name    : actuarial_alterationRevisedReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:04:50.666863+00:00
-- url     : https://prove2.me/theorems/6d18f010-60ea-45d9-9dc9-d762829ef25a
-- title:
--   Prospective reserve and premium difference: alterationRevisedReserve
-- statement:
--   Reserve after replacing the remaining gross or net premium by a new level value under unchanged benefits. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V' = B-P'a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def alterationRevisedReserve (futureBenefits newPremium premiumAnnuity : ℝ) : ℝ := futureBenefits - newPremium*premiumAnnuity

end ActuarialValuation


