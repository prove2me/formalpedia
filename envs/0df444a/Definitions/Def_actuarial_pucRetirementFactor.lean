-- Prove2me | Definitions.Def_actuarial_pucRetirementFactor
-- name    : actuarial_pucRetirementFactor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:04:04.549594+00:00
-- url     : https://prove2.me/theorems/aca2f673-c2a4-49be-9cfe-f81b3cf5b85b
-- title:
--   Actuarial liability and normal cost: pucRetirementFactor
-- statement:
--   The probability-discount-annuity factor converts an annual retirement pension into valuation-date benefit PV. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f={}_np_xv^na_R
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pucRetirementFactor (survival discount annuity : ℝ) : ℝ := survival * discount * annuity

end ActuarialValuation


