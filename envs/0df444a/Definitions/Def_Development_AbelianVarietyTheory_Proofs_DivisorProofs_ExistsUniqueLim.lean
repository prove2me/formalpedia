-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueLim
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueLim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:17.823173+00:00
-- url     : https://prove2.me/theorems/f6b7611d-ec7c-45a4-bb9e-fbfcc8711f61
-- title:
--   Exists Unique Lim
-- statement:
--   Definitions and structural lemmas for Exists Unique Lim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueLim.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AdicPt
open IsLocalRing
variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}
end GlobalTheory.AdicPt


