-- Prove2me | Definitions.Def_O3_Stage2RouteD
-- name    : O3_Stage2RouteD
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:11:04.702294+00:00
-- url     : https://prove2.me/theorems/49c278f3-71ef-4ecb-8a42-34d306b29186
-- title:
--   Stage2 Route D
-- statement:
--   Definitions and structural lemmas for Stage2 Route D, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean

import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open scoped BigOperators
namespace O3.Stage2RouteD
noncomputable def weightVector (q : ℝ) {d : ℕ} (z : Point d) : Point d :=
  fun i ↦ |z i| ^ (q - 2)
noncomputable def squareVector {d : ℕ} (h : Point d) : Point d :=
  fun i ↦ (h i) ^ (2 : ℕ)
end O3.Stage2RouteD


