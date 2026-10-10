-- Prove2me | Definitions.Def_actuarial_kmRestrictedLife
-- name    : actuarial_kmRestrictedLife
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:47.107029+00:00
-- url     : https://prove2.me/theorems/e30dfa25-3541-46b6-a102-c04872215fb5
-- title:
--   Greenwood uncertainty and finite restricted survival: kmRestrictedLife
-- statement:
--   The finite discrete restricted expected survival duration is the sum of interval-start survival estimates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   RMST_n=\sum_{t<n}\widehat S_t
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival

namespace ActuarialValuation

noncomputable def kmRestrictedLife (risk deaths : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, kmSurvival risk deaths t

end ActuarialValuation


