-- Prove2me | Definitions.Def_actuarial_jlMortalityProfit
-- name    : actuarial_jlMortalityProfit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:01.441671+00:00
-- url     : https://prove2.me/theorems/c642a267-545b-4d65-8516-0fcc2697d9ba
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlMortalityProfit
-- statement:
--   Mortality profit equals expected strain less observed state strain. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlExpectedStrain
import Definitions.Def_actuarial_jlActualStrain

namespace ActuarialValuation

noncomputable def jlMortalityProfit (px py : ℝ) (pay next : Fin 4 → ℝ) (available : ℝ) (state : Fin 4) : ℝ := jlExpectedStrain px py pay next available-jlActualStrain state pay next available

end ActuarialValuation


