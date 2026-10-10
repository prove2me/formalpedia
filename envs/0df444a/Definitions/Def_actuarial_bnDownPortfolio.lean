-- Prove2me | Definitions.Def_actuarial_bnDownPortfolio
-- name    : actuarial_bnDownPortfolio
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:53.295738+00:00
-- url     : https://prove2.me/theorems/52053459-5f92-43e7-bd6c-c1b6a68376b3
-- title:
--   Explicit self-financing hedge and European option replication: bnDownPortfolio
-- statement:
--   Terminal down-state payoff of the same strategy.
--
--   Mathematical relation:
--
--   $$
--   s*d*shares+R*cash
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnDownPortfolio (s R d shares cash : ℝ) : ℝ := s*d*shares+R*cash

end ActuarialValuation


