-- Prove2me | Definitions.Def_actuarial_bnRiskNeutralProb
-- name    : actuarial_bnRiskNeutralProb
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:23.076707+00:00
-- url     : https://prove2.me/theorems/b8e577c1-c55b-49b2-af9f-a25891c6728f
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnRiskNeutralProb
-- statement:
--   The unique up-state martingale probability q in a one-period binomial stock market with growth factor R, up factor u and down factor d; valid when d<R<u.
--
--   Mathematical relation:
--
--   $$
--   (R-d)/(u-d)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnRiskNeutralProb (u d R : ℝ) : ℝ := (R-d)/(u-d)

end ActuarialValuation


