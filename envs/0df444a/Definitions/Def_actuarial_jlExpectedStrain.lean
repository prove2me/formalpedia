-- Prove2me | Definitions.Def_actuarial_jlExpectedStrain
-- name    : actuarial_jlExpectedStrain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:24.634671+00:00
-- url     : https://prove2.me/theorems/4997d253-59d1-4160-84db-929b33460bde
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlExpectedStrain
-- statement:
--   Full expected joint death strain including changes to each survivor reserve. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlStateStrain
import Definitions.Def_actuarial_jlProbability

namespace ActuarialValuation

noncomputable def jlExpectedStrain (px py : ℝ) (pay next : Fin 4 → ℝ) (available : ℝ) : ℝ := ∑ s : Fin 4, jlProbability px py s*jlStateStrain (pay s) (next s) available

end ActuarialValuation


