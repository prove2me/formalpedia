-- Prove2me | Definitions.Def_actuarial_alterationPaidUpScaledValue
-- name    : actuarial_alterationPaidUpScaledValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:05:24.964124+00:00
-- url     : https://prove2.me/theorems/3bb68021-f88f-4f8b-b545-1ebbb0ad71c0
-- title:
--   Paid-up insurance and equivalent cover: alterationPaidUpScaledValue
-- statement:
--   Value of benefits scaled across all future contingencies using a uniform paid-up cover percentage. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PV=zB
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def alterationPaidUpScaledValue (fraction originalBenefitsPV : ℝ) : ℝ := fraction*originalBenefitsPV

end ActuarialValuation


