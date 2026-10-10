-- Prove2me | Definitions.Def_actuarial_bnCall
-- name    : actuarial_bnCall
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:00.772092+00:00
-- url     : https://prove2.me/theorems/373de5e1-9d99-414c-8b28-d735ae546f84
-- title:
--   Explicit self-financing hedge and European option replication: bnCall
-- statement:
--   European call-option terminal exercise payoff with underlying price s and strike k.
--
--   Mathematical relation:
--
--   $$
--   max (s-k) 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnCall (s k : ℝ) : ℝ := max (s-k) 0

end ActuarialValuation


