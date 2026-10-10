-- Prove2me | Definitions.Def_actuarial_bnHedgeShares
-- name    : actuarial_bnHedgeShares
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:16.497982+00:00
-- url     : https://prove2.me/theorems/64415863-be95-4ebe-9581-761fa6a59b19
-- title:
--   Explicit self-financing hedge and European option replication: bnHedgeShares
-- statement:
--   Shares required to hedge two contingent payments when current stock s≠0 and u≠d.
--
--   Mathematical relation:
--
--   $$
--   (xu-xd)/(s*(u-d))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnHedgeShares (s u d xu xd : ℝ) : ℝ := (xu-xd)/(s*(u-d))

end ActuarialValuation


