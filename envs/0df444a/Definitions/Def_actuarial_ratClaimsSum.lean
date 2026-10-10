-- Prove2me | Definitions.Def_actuarial_ratClaimsSum
-- name    : actuarial_ratClaimsSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T08:43:42.823059+00:00
-- url     : https://prove2.me/theorems/00081baa-ef82-4d48-9805-61f98338b51e
-- title:
--   Exposure, observed claims and indicated pure premiums: ratClaimsSum
-- statement:
--   Observed total claim costs across the same classes or experience cells. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   L=\sum_{i<n}L_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ratClaimsSum (l : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, l i

end ActuarialValuation


