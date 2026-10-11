-- Prove2me | Definitions.Def_actuarial_jlGuaranteedPayment
-- name    : actuarial_jlGuaranteedPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:14.219198+00:00
-- url     : https://prove2.me/theorems/6ea19b9d-fae7-46e3-92b0-b2a1a8d63e99
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlGuaranteedPayment
-- statement:
--   One-year guaranteed benefit paid with certainty inside guarantee period and otherwise contingent on survival. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pi_{\text{mort}}=\sum_s p_s D_s-D_{\text{observed}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace ActuarialValuation

noncomputable def jlGuaranteedPayment (memberSurvival benefit guarantee : ℝ) : ℝ := guarantee*benefit+(1-guarantee)*memberSurvival*benefit

end ActuarialValuation


