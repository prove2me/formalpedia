-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:51.716136+00:00
-- url     : https://prove2.me/theorems/5249b5ac-8a92-4041-8090-4e69957ed6a7
-- title:
--   Unit On Product Eq One
-- statement:
--   Definitions and structural lemmas for Unit On Product Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
namespace GlobalTheory.PrimitiveUnitProduct
section Gauss
variable {K A O F : Type} [Field K] [CommRing A] [Algebra K A] [CommRing O] [IsDomain O]
  [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K O] [Algebra K F]
  [IsScalarTower K O F]
end Gauss
end GlobalTheory.PrimitiveUnitProduct


