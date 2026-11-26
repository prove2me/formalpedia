-- Prove2me | Definitions.Def_O3_Stage2BelowGeometry
-- name    : O3_Stage2BelowGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:34:42.713576+00:00
-- url     : https://prove2.me/theorems/e61e595c-0e87-5c12-80cb-1a2bc5a108de
-- title:
--   Stage2 Below Geometry
-- statement:
--   Definitions and structural lemmas for Stage2 Below Geometry, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2BelowGeometry.lean

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
set_option autoImplicit true
namespace O3
namespace Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
noncomputable def smoothRemainder (q : ℝ) {d : ℕ}
    (u h : Point d) (t : ℝ) : ℝ :=
  squaredLpEnergy q (u + t • h) -
    ((q - 1) / 2) * t ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ)
noncomputable def smoothRemainderDeriv (q : ℝ) {d : ℕ}
    (u h : Point d) (t : ℝ) : ℝ :=
  pairing (dualityMap q (u + t • h)) h -
    (q - 1) * t * (lpNorm q h) ^ (2 : ℕ)
end Stage2Closure
end O3


