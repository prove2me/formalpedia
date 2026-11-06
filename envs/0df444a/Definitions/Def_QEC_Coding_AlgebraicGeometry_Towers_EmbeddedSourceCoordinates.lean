-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
-- name    : QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:43.742089+00:00
-- url     : https://prove2.me/theorems/ef03eb0b-3ecd-4ffd-88ad-43905f7ce511
-- title:
--   Embedded Source Coordinates
-- statement:
--   Definitions and structural lemmas for Embedded Source Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedSourceCoordinates.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans

set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
theorem finite_separable_over_mapped_subfield (K : IntermediateField F256 F)
    [FiniteDimensional K F] [Algebra.IsSeparable K F] :
    FiniteDimensional (K.map (IsScalarTower.toAlgHom F256 F E)) E ∧
      Algebra.IsSeparable (K.map (IsScalarTower.toAlgHom F256 F E)) E := by
  let f := IsScalarTower.toAlgHom F256 F E
  let j : K →ₐ[F256] E := f.comp K.val
  let J := j.fieldRange
  letI : Algebra K E := j.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K E := FiniteDimensional.trans K F E
  letI : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  let jJ : K →ₐ[F256] J := j.codRestrict J.toSubalgebra (fun x => ⟨x, rfl⟩)
  letI : Algebra K J := jJ.toRingHom.toAlgebra
  letI : IsScalarTower K J E := IsScalarTower.of_algebraMap_eq' rfl
  have hresult : FiniteDimensional J E ∧ Algebra.IsSeparable J E :=
    ⟨Module.Finite.of_restrictScalars_finite K J E,
      Algebra.isSeparable_tower_top_of_isSeparable K J E⟩
  have hJ : J = K.map f := by
    change (f.comp K.val).fieldRange = K.map f
    rw [← AlgHom.map_fieldRange, IntermediateField.fieldRange_val]
  rw [hJ] at hresult
  exact hresult
end
noncomputable section
variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]
theorem embeddedSourceCoordinates_finite_separable (i : ℕ) :
    FiniteDimensional F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E ∧
      Algebra.IsSeparable F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E := by
  have h := finite_separable_over_mapped_subfield (E := E) F256⟮sourceCoordinates m i⟯
  have heq : (F256⟮sourceCoordinates m i⟯).map (IsScalarTower.toAlgHom F256 (SourceField m) E) =
      F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [heq] at h
  exact h
scoped instance embeddedSourceCoordinates_finite (i : ℕ) :
    FiniteDimensional F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E :=
  (embeddedSourceCoordinates_finite_separable m i).1
scoped instance embeddedSourceCoordinates_separable (i : ℕ) :
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E :=
  (embeddedSourceCoordinates_finite_separable m i).2
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


