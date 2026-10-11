-- Prove2me | Definitions.Def_actuarial_jlReversionaryPayment
-- name    : actuarial_jlReversionaryPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:07.310288+00:00
-- url     : https://prove2.me/theorems/be8c302e-56bb-4a70-b562-f813b4de505d
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlReversionaryPayment
-- statement:
--   Contingent one-year spouse's pension triggered by the member dying before a surviving spouse. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def jlReversionaryPayment (px py spouseBenefit : ℝ) : ℝ := (1-px)*py*spouseBenefit

end ActuarialValuation


