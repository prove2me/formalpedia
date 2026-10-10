-- Prove2me | Definitions.Def_actuarial_kmFailure
-- name    : actuarial_kmFailure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:36.294238+00:00
-- url     : https://prove2.me/theorems/8a2d254d-7823-425f-8443-58d0c6d88aff
-- title:
--   Kaplan-Meier product-limit survival: kmFailure
-- statement:
--   Cumulative estimated failure probability is the complement of product-limit survival. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \widehat F_n=1-\widehat S_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival

namespace ActuarialValuation

noncomputable def kmFailure (risk deaths : ℕ → ℝ) (n : ℕ) : ℝ := 1 - kmSurvival risk deaths n

end ActuarialValuation


