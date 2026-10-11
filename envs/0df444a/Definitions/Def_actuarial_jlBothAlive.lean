-- Prove2me | Definitions.Def_actuarial_jlBothAlive
-- name    : actuarial_jlBothAlive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:05.576995+00:00
-- url     : https://prove2.me/theorems/08979c65-1b43-48a7-92ba-56de55eb187b
-- title:
--   Independent joint-life outcomes and probabilities: jlBothAlive
-- statement:
--   Year-end probability of two survivors under independent lifetimes. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def jlBothAlive (px py : ℝ) : ℝ := px*py

end ActuarialValuation


