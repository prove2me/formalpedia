-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
-- name    : QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:32:37.715132+00:00
-- url     : https://prove2.me/theorems/aae38d45-770d-4661-9575-33eb7c8dc582
-- title:
--   Embedded WSeed
-- statement:
--   Definitions and structural lemmas for Embedded WSeed, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
end
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]
theorem embeddedSourceW_finite_separable :
    FiniteDimensional F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E ∧
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E := by
  letI : Algebra (RatFunc F256) E :=
    ((algebraMap (SourceField m) E).comp (algebraMap (RatFunc F256) (SourceField m))).toAlgebra
  letI : IsScalarTower (RatFunc F256) (SourceField m) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F256 (RatFunc F256) E := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    change algebraMap F256 E c = algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) (algebraMap F256 (RatFunc F256) c))
    rw [← IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceField m),
      ← IsScalarTower.algebraMap_apply F256 (SourceField m) E])
  letI : FiniteDimensional (RatFunc F256) E :=
    FiniteDimensional.trans (RatFunc F256) (SourceField m) E
  letI : Algebra.IsSeparable (RatFunc F256) E :=
    Algebra.IsSeparable.trans (RatFunc F256) (SourceField m) E
  letI : FiniteDimensional F256⟮galoisBaseW⟯ (RatFunc F256) :=
    inferInstanceAs (FiniteDimensional SourceGaloisWField (RatFunc F256))
  letI : Algebra.IsSeparable F256⟮galoisBaseW⟯ (RatFunc F256) :=
    inferInstanceAs (Algebra.IsSeparable SourceGaloisWField (RatFunc F256))
  have h := finite_separable_over_mapped_subfield (E := E) F256⟮galoisBaseW⟯
  have heq : (F256⟮galoisBaseW⟯).map (IsScalarTower.toAlgHom F256 (RatFunc F256) E) =
      F256⟮algebraMap (SourceField m) E
        (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [heq] at h
  exact h
scoped instance embeddedSourceW_finite :
    FiniteDimensional F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E :=
  (embeddedSourceW_finite_separable m).1
scoped instance embeddedSourceW_separable :
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E :=
  (embeddedSourceW_finite_separable m).2
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


