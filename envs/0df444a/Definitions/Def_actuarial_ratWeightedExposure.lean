-- Prove2me | Definitions.Def_actuarial_ratWeightedExposure
-- name    : actuarial_ratWeightedExposure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:16:07.516321+00:00
-- url     : https://prove2.me/theorems/54122462-7e00-4b4e-985f-64c402e85d8d
-- title:
--   Class relativities and aggregate technical premium: ratWeightedExposure
-- statement:
--   Relative-weighted earned exposure is the denominator in class-mix base rate calibration. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   W=\sum_i e_ir_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratWeightedExposure (e relativity : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, e i * relativity i

end ActuarialValuation


