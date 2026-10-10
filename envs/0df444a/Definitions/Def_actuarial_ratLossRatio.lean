-- Prove2me | Definitions.Def_actuarial_ratLossRatio
-- name    : actuarial_ratLossRatio
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:22:25.561235+00:00
-- url     : https://prove2.me/theorems/72972d34-8d90-4d91-ad70-be2c1e808e48
-- title:
--   Base rate calibration and technical premium adequacy: ratLossRatio
-- statement:
--   Aggregate observed loss ratio is measured against the premiums earned on a matched basis. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   LR=L/P
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratLossRatio (claims premium : ℝ) : ℝ := claims / premium

end ActuarialValuation


