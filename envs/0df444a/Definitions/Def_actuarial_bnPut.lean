-- Prove2me | Definitions.Def_actuarial_bnPut
-- name    : actuarial_bnPut
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:12.433452+00:00
-- url     : https://prove2.me/theorems/c3910844-df6a-46af-a041-1d6f69181ff7
-- title:
--   Explicit self-financing hedge and European option replication: bnPut
-- statement:
--   European put-option terminal exercise payoff with underlying price s and strike k.
--
--   Mathematical relation:
--
--   $$
--   max (k-s) 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnPut (s k : ℝ) : ℝ := max (k-s) 0

end ActuarialValuation


