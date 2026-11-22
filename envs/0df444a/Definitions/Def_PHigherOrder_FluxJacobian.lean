-- Prove2me | Definitions.Def_PHigherOrder_FluxJacobian
-- name    : PHigherOrder_FluxJacobian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:10:06.569906+00:00
-- url     : https://prove2.me/theorems/d72215a2-d38c-4e57-8498-1d1a615e319f
-- title:
--   Flux Jacobian
-- statement:
--   Definitions and structural lemmas for Flux Jacobian, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobian.lean

import Definitions.Def_PHigherOrder_PFlux
set_option autoImplicit false
noncomputable def FluxJacobian (p : ℝ) (ξ : Plane) : Plane →L[ℝ] Plane :=
  ‖ξ‖ ^ (p - 2) • (ContinuousLinearMap.id ℝ Plane
    + ((p - 2) / ‖ξ‖ ^ 2) • (innerSL ℝ ξ).smulRight ξ)


