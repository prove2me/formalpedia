-- Prove2me | Definitions.Def_actuarial_jlFirstDeath
-- name    : actuarial_jlFirstDeath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:52.935415+00:00
-- url     : https://prove2.me/theorems/5baf9f22-0d0d-42b3-8853-3c0d7c7437ab
-- title:
--   Independent joint-life outcomes and probabilities: jlFirstDeath
-- statement:
--   Probability of at least one death during a year. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   p_{xy}=p_xp_y,\quad p_{x\dagger y}=(1-p_x)p_y
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothAlive

namespace ActuarialValuation

noncomputable def jlFirstDeath (px py : ℝ) : ℝ := 1-jlBothAlive px py

end ActuarialValuation


