-- Prove2me | Definitions.Def_actuarial_pucActuarialLiability
-- name    : actuarial_pucActuarialLiability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:04:16.193396+00:00
-- url     : https://prove2.me/theorems/86a73415-0b7e-45bf-92fd-4d7c41914d2e
-- title:
--   Actuarial liability and normal cost: pucActuarialLiability
-- statement:
--   Projected unit credit pension liability for service already attributed at the valuation date. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   AL_n=B_nf
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit

namespace ActuarialValuation

noncomputable def pucActuarialLiability (unit : ℕ → ℝ) (n : ℕ) (f : ℝ) : ℝ := pucAccruedBenefit unit n * f

end ActuarialValuation


