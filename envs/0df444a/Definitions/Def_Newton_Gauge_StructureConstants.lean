-- Prove2me | Definitions.Def_Newton_Gauge_StructureConstants
-- name    : Newton_Gauge_StructureConstants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:38.882251+00:00
-- url     : https://prove2.me/theorems/f27dce1f-42d8-48ef-ac1b-ab314600f431
-- title:
--   Structure Constants
-- statement:
--   Definitions and structural lemmas for Structure Constants, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean

import Definitions.Def_Newton_Gauge_LieAlgebra
set_option autoImplicit false
open Matrix
namespace Newton
variable {N : ℕ}
noncomputable def adjointAd (A : SuNAlgebra N) (B : SuNAlgebra N) : SuNAlgebra N :=
  ⁅A, B⁆
namespace adjointAd
end adjointAd
noncomputable def adjointAd2 (A B : SuNAlgebra N) : SuNAlgebra N :=
  adjointAd A (adjointAd A B)
end Newton


