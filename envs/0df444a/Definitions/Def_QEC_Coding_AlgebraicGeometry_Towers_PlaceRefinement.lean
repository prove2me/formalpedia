-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:17:18.723701+00:00
-- url     : https://prove2.me/theorems/6c14051c-7ddd-4bf3-9d5b-27f795b32824
-- title:
--   Place Refinement
-- statement:
--   Definitions and structural lemmas for Place Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
abbrev PlaceNormalizedRefinement
    (F : Type*) [_root_.Field F] [Algebra F256 F] [Algebra F E]
    [IsScalarTower F256 F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E) (J L : IntermediateField F E) : Prop :=
  NormalizedRefinement (AmbientPlaceModels.baseRing F Q) F E
    (AmbientPlaceModels.prime F Q) J L
variable (F K : Type*) [_root_.Field F] [_root_.Field K]
    [Algebra F256 F] [Algebra F256 K] [Algebra F K] [Algebra K E] [Algebra F E]
    [IsScalarTower F K E] [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (Q : GlobalPlace F256 E)
end
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E)
scoped instance intermediateBase_separable (L : IntermediateField F E) :
    Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable F L E
scoped instance intermediateBase_constantTower (L : IntermediateField F E) :
    IsScalarTower F256 L E := IsScalarTower.of_algebraMap_eq' rfl
end
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
def PlaceNormalizedExtension (Q : GlobalPlace F256 E)
    (K L : IntermediateField F256 E)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  ∃ h : K ≤ L, PlaceNormalizedRefinement K Q ⊥ (IntermediateField.extendScalars h)
variable (Q : GlobalPlace F256 E) {K L M : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


