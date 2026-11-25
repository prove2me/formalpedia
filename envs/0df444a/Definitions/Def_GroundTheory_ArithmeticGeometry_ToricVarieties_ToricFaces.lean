-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:47.137776+00:00
-- url     : https://prove2.me/theorems/c31ad043-df5d-463a-a220-b0424bcf1573
-- title:
--   Toric Faces
-- statement:
--   Definitions and structural lemmas for Toric Faces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
end GroundTheory.Arith.Toric


