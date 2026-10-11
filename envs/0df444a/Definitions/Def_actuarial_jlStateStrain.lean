-- Prove2me | Definitions.Def_actuarial_jlStateStrain
-- name    : actuarial_jlStateStrain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:41.023597+00:00
-- url     : https://prove2.me/theorems/da3b4f51-f3fd-4239-8205-4d4db0389f01
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlStateStrain
-- statement:
--   Outcome-specific cost in excess of accumulated initial reserve plus premium. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def jlStateStrain (benefit nextReserve available : ℝ) : ℝ := benefit+nextReserve-available

end ActuarialValuation


