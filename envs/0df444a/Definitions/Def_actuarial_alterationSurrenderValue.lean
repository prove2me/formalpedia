-- Prove2me | Definitions.Def_actuarial_alterationSurrenderValue
-- name    : actuarial_alterationSurrenderValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:05:36.545753+00:00
-- url     : https://prove2.me/theorems/66c71980-cc87-4e7e-bd05-7021dc423d7a
-- title:
--   Surrender deductions and policy value comparisons: alterationSurrenderValue
-- statement:
--   Simplified cash surrender value after a nonnegative deduction from the prospective reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SV=V-c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def alterationSurrenderValue (reserve deduction : ℝ) : ℝ := reserve - deduction

end ActuarialValuation


