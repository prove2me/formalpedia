-- Prove2me | Definitions.Def_actuarial_bnHedgeCash
-- name    : actuarial_bnHedgeCash
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:26.75104+00:00
-- url     : https://prove2.me/theorems/e87bfb5c-08db-4142-8677-eab88291caf5
-- title:
--   Explicit self-financing hedge and European option replication: bnHedgeCash
-- statement:
--   Risk-free cash deposit at time zero used with hedge shares to replicate state payoffs, requiring nonzero R and u-d.
--
--   Mathematical relation:
--
--   $$
--   (u*xd-d*xu)/(R*(u-d))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnHedgeCash (R u d xu xd : ℝ) : ℝ := (u*xd-d*xu)/(R*(u-d))

end ActuarialValuation


