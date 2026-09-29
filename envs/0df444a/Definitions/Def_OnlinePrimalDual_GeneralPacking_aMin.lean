-- Prove2me | Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
-- name    : OnlinePrimalDual_GeneralPacking_aMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:08:46.560086+00:00
-- url     : https://prove2.me/theorems/dc7e7925-fb3f-4644-9420-70626672764c
-- title:
--   Per-variable minimum non-zero coefficient a_i(min)
-- statement:
--   `aMin inst i := a_i(min) = min_k{a(i,k) | a(i,k) ≠ 0}`, the smallest non-zero coefficient of
--   primal variable `i` across every constraint (`0`, a documented junk value never exercised
--   where used, if `i` has no non-zero coefficient).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 249, Theorem 14.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

/-- `aᵢ(min) = minₖ{a(i,k) ∣ a(i,k) ≠ 0}` (Buchbinder & Naor, FnT TCS 2009, Theorem 14.1, p. 249):
the smallest *non-zero* coefficient of primal variable `i` across every constraint, `0` (a junk
value, never exercised where this quantity is actually used — see `STATUS.md`) if `i` has no
non-zero coefficient at all. -/
noncomputable def aMin {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (inst : GeneralInstance I J) (i : I) : ℝ :=
  if h : ((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i)).Nonempty then
    (((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i))).min' h
  else 0

end OnlinePrimalDual.GeneralPacking


