-- Prove2me | Definitions.Def_actuarial_bnUpPortfolio
-- name    : actuarial_bnUpPortfolio
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:44.958624+00:00
-- url     : https://prove2.me/theorems/83fe7270-ea76-4fc9-9e14-017a04cdd40a
-- title:
--   Explicit self-financing hedge and European option replication: bnUpPortfolio
-- statement:
--   Terminal up-state payoff of a buy-and-hold self-financing stock-and-bank account strategy.
--
--   Mathematical relation:
--
--   $$
--   s*u*shares+R*cash
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnUpPortfolio (s R u shares cash : ℝ) : ℝ := s*u*shares+R*cash

end ActuarialValuation


