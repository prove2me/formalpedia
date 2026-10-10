-- Prove2me | Definitions.Def_actuarial_kmGreenwoodTerm
-- name    : actuarial_kmGreenwoodTerm
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:00.820013+00:00
-- url     : https://prove2.me/theorems/4a41752c-85f7-49ce-8c13-b56d742cc815
-- title:
--   Greenwood uncertainty and finite restricted survival: kmGreenwoodTerm
-- statement:
--   Greenwood's variance adjustment at a death time requires positive risk remaining after deaths. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_t=d_t/[r_t(r_t-d_t)]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 267. Society of Actuaries, Mortality Differences by Handedness, Transactions of the Society of Actuaries 45 (1993), p. 267, https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf; Kaplan and Meier, Nonparametric Estimation from Incomplete Observations (1958), Journal of the American Statistical Association 53, pp. 457-481. Parent topic: At-risk exposure and deaths with administrative censoring, product-limit survival estimator and Greenwood variance correction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.soa.org/globalassets/assets/library/research/transactions-of-society-of-actuaries/1990-95/1993/january/tsa93v459.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def kmGreenwoodTerm (deaths risk : ℝ) : ℝ := deaths / (risk * (risk-deaths))

end ActuarialValuation


