-- Prove2me | Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
-- name    : OnlinePrimalDual_GeneralPacking_aMax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:08:22.252284+00:00
-- url     : https://prove2.me/theorems/fc55f53f-c63d-43c3-8804-a0d6d1600e7c
-- title:
--   Per-variable maximum coefficient a_i(max)
-- statement:
--   `aMax inst i := a_i(max) = max_k{a(i,k)}`, the largest coefficient of primal variable `i`
--   across every constraint.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 249, Theorem 14.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

/-- `aᵢ(max) = maxₖ{a(i,k)}` (Buchbinder & Naor, FnT TCS 2009, Theorem 14.1, p. 249): the largest
coefficient of primal variable `i` across every constraint. -/
noncomputable def aMax {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (inst : GeneralInstance I J) (i : I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (inst.a i)

end OnlinePrimalDual.GeneralPacking


