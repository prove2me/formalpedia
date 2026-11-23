-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:05.242347+00:00
-- url     : https://prove2.me/theorems/91e0dc2c-3f42-4e70-beee-15dfdbcfc756
-- title:
--   Is Affine Open Inf Of Is Separated
-- statement:
--   Definitions and structural lemmas for Is Affine Open Inf Of Is Separated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KuennethOne
section General
open TopologicalSpace TensorProduct
variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}
include H
end General
end GlobalTheory.KuennethOne


