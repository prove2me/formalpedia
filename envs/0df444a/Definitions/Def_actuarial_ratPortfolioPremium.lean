-- Prove2me | Definitions.Def_actuarial_ratPortfolioPremium
-- name    : actuarial_ratPortfolioPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:32.253424+00:00
-- url     : https://prove2.me/theorems/5d248e0f-bdba-4288-888e-2bed34abb87a
-- title:
--   Class relativities and aggregate technical premium: ratPortfolioPremium
-- statement:
--   Portfolio technical premium aggregates the individual class pure premiums at the common base rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P=\sum_i e_i b r_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

namespace ActuarialValuation

noncomputable def ratPortfolioPremium (e relativity : ℕ → ℝ) (n : ℕ) (base : ℝ) : ℝ := ∑ i ∈ Finset.range n, ratClassPremium (e i) base (relativity i)

end ActuarialValuation


