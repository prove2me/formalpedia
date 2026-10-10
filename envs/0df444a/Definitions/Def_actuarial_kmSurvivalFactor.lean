-- Prove2me | Definitions.Def_actuarial_kmSurvivalFactor
-- name    : actuarial_kmSurvivalFactor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:23:43.56401+00:00
-- url     : https://prove2.me/theorems/46ac587d-45ef-4e87-bfff-40314c7c55e6
-- title:
--   Kaplan-Meier product-limit survival: kmSurvivalFactor
-- statement:
--   Survival probability across a death time equals one minus the observed conditional mortality fraction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_t=1-d_t/r_t
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmDeathHazard

namespace ActuarialValuation

noncomputable def kmSurvivalFactor (deaths risk : ℝ) : ℝ := 1 - kmDeathHazard deaths risk

end ActuarialValuation


