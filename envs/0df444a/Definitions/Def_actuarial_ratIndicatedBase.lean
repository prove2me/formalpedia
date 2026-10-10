-- Prove2me | Definitions.Def_actuarial_ratIndicatedBase
-- name    : actuarial_ratIndicatedBase
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:45.807301+00:00
-- url     : https://prove2.me/theorems/81703087-7519-446b-a448-1301c7645275
-- title:
--   Base rate calibration and technical premium adequacy: ratIndicatedBase
-- statement:
--   Indicated base rate equals the projected aggregate claim cost divided by positive relativity-weighted exposure. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   b^*=T/W
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratIndicatedBase (target weightedExposure : ℝ) : ℝ := target / weightedExposure

end ActuarialValuation


