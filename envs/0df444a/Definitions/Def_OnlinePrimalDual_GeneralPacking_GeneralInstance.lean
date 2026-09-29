-- Prove2me | Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
-- name    : OnlinePrimalDual_GeneralPacking_GeneralInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:07:44.379135+00:00
-- url     : https://prove2.me/theorems/fc1ee1a4-6205-40f7-801d-9dbb4604077a
-- title:
--   The general packing-covering instance data
-- statement:
--   `GeneralInstance I J` bundles: a finite set `I` of primal (covering) variables with positive
--   cost coefficients `c`, and a finite set `J` of dual (packing) variables/covering constraints,
--   with non-negative coefficients `a(i,j)` for every pair — generalizing Chapter 4's framework
--   from `a(i,j) ∈ {0,1}` to arbitrary non-negative reals.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 246-247, Fig. 14.1

import Mathlib

namespace OnlinePrimalDual.GeneralPacking

/-- The general packing-covering instance data (Buchbinder & Naor, FnT TCS 2009, Section 14,
p. 246-247, Fig. 14.1): a finite set `I` of primal (covering) variables with positive cost
coefficients `c`, and a finite set `J` of dual (packing) variables/covering constraints, each
pair `(i, j)` carrying a non-negative coefficient `a(i,j)` — the generalization of Chapter 4's
framework from `a(i,j) ∈ {0,1}` to arbitrary non-negative reals. -/
structure GeneralInstance (I J : Type*) [Fintype I] [Fintype J] where
  /-- `a i j` is the (non-negative) coefficient of primal variable `i` in constraint `j`. -/
  a : I → J → ℝ
  ha_nonneg : ∀ i j, 0 ≤ a i j
  /-- The (positive) cost coefficients of the covering objective. -/
  c : I → ℝ
  hc_pos : ∀ i, 0 < c i

end OnlinePrimalDual.GeneralPacking


