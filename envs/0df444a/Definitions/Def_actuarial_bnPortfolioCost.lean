-- Prove2me | Definitions.Def_actuarial_bnPortfolioCost
-- name    : actuarial_bnPortfolioCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:35.796631+00:00
-- url     : https://prove2.me/theorems/0ff6f884-caf3-42a1-9361-3751cbd654a0
-- title:
--   Explicit self-financing hedge and European option replication: bnPortfolioCost
-- statement:
--   Market value of a stock-and-cash replicating portfolio at inception.
--
--   Mathematical relation:
--
--   $$
--   s*shares+cash
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnPortfolioCost (s shares cash : ℝ) : ℝ := s*shares+cash

end ActuarialValuation


