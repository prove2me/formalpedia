-- Prove2me | Definitions.Def_actuarial_kmGreenwoodSum
-- name    : actuarial_kmGreenwoodSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:13.663104+00:00
-- url     : https://prove2.me/theorems/d18b5f62-e870-4bbc-9c44-500290897065
-- title:
--   Greenwood uncertainty and finite restricted survival: kmGreenwoodSum
-- statement:
--   Cumulative Greenwood uncertainty coefficient sums the death-to-remaining-risk ratios. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_n=\sum_{t<n}d_t/[r_t(r_t-d_t)]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodTerm

namespace ActuarialValuation

noncomputable def kmGreenwoodSum (risk deaths : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, kmGreenwoodTerm (deaths t) (risk t)

end ActuarialValuation


