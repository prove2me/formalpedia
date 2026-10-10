-- Prove2me | Definitions.Def_actuarial_ratRevenueSurplus
-- name    : actuarial_ratRevenueSurplus
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:51.726772+00:00
-- url     : https://prove2.me/theorems/6d297c14-a1a0-4bc1-a0d8-50d1bf668b83
-- title:
--   Base rate calibration and technical premium adequacy: ratRevenueSurplus
-- statement:
--   Technical revenue margin before expenses and risk loading relative to projected insured claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S(b)=bW-T
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratRevenueSurplus (target weighted base : ℝ) : ℝ := base * weighted - target

end ActuarialValuation


