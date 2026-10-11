-- Prove2me | Definitions.Def_actuarial_jlProbability
-- name    : actuarial_jlProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:59.114981+00:00
-- url     : https://prove2.me/theorems/7aed3eaa-1f92-4053-89e6-2f0625a9610b
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlProbability
-- statement:
--   Actual four-state joint survivor/death probability distribution. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlBothAlive
import Definitions.Def_actuarial_jlOnlyXAlive
import Definitions.Def_actuarial_jlOnlyYAlive
import Definitions.Def_actuarial_jlBothDead

namespace ActuarialValuation

noncomputable def jlProbability (px py : ℝ) (state : Fin 4) : ℝ := if state=0 then jlBothAlive px py else if state=1 then jlOnlyXAlive px py else if state=2 then jlOnlyYAlive px py else jlBothDead px py

end ActuarialValuation


