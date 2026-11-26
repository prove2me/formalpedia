-- Prove2me | Definitions.Def_O3_GeometryExperimental
-- name    : O3_GeometryExperimental
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:52:59.836418+00:00
-- url     : https://prove2.me/theorems/080e29db-8a66-4a41-a5f6-f5564113b54a
-- title:
--   Geometry Experimental
-- statement:
--   Definitions and structural lemmas for Geometry Experimental, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean

import Definitions.Def_O3_Geometry
set_option autoImplicit true
namespace O3.Experimental
noncomputable def scalarJ (p u : ℝ) : ℝ := |u| ^ (p - 2) * u
noncomputable def scalarEnergy (p x : ℝ) : ℝ := |x| ^ p / p
end O3.Experimental
namespace O3
end O3


