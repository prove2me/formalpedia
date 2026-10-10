-- Prove2me | Definitions.Def_actuarial_pucFutureBenefit
-- name    : actuarial_pucFutureBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:03:39.1649+00:00
-- url     : https://prove2.me/theorems/becb2ca9-f17b-4936-89a7-d35665c333fe
-- title:
--   Projected service and accrued benefits: pucFutureBenefit
-- statement:
--   Additional projected pension benefit earned during m future years after n completed years. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_{n,m}=\sum_{t<m}b_{n+t}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pucFutureBenefit (unit : ℕ → ℝ) (n m : ℕ) : ℝ := ∑ t ∈ Finset.range m, unit (n+t)

end ActuarialValuation


