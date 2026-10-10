-- Prove2me | Definitions.Def_actuarial_ratRateChange
-- name    : actuarial_ratRateChange
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:22:14.376426+00:00
-- url     : https://prove2.me/theorems/ee78afd3-3854-4fe0-9471-814ea24cfc65
-- title:
--   Base rate calibration and technical premium adequacy: ratRateChange
-- statement:
--   Relative base rate change uses an explicitly nonzero existing base rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta=b_{new}/b_{old}-1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratRateChange (newRate oldRate : ℝ) : ℝ := newRate / oldRate - 1

end ActuarialValuation


