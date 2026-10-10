-- Prove2me | Definitions.Def_actuarial_ratClassPremium
-- name    : actuarial_ratClassPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T08:44:18.813531+00:00
-- url     : https://prove2.me/theorems/152c9841-5d30-4800-8051-e2addb4d24e9
-- title:
--   Class relativities and aggregate technical premium: ratClassPremium
-- statement:
--   Pure class premium is exposure multiplied by base loss rate and relative cost multiplier. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_i=e_i b r_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratClassPremium (exposure base relativity : ℝ) : ℝ := exposure * base * relativity

end ActuarialValuation


