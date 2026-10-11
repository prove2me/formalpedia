-- Prove2me | Definitions.Def_actuarial_jlPostPremiumFund
-- name    : actuarial_jlPostPremiumFund
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:31.599198+00:00
-- url     : https://prove2.me/theorems/c79e8f9c-82d1-4c4f-97fe-6eabc94b87dc
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlPostPremiumFund
-- statement:
--   Fund available immediately before claims, reflecting gross or net premiums and annual interest. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   D_{s}=B_s+V_s-(V_0+P)(1+i)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace ActuarialValuation

noncomputable def jlPostPremiumFund (reserve premium interest : ℝ) : ℝ := (reserve+premium)*(1+interest)

end ActuarialValuation


