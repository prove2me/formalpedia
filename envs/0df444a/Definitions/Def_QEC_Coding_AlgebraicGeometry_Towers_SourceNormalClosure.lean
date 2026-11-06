-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:21:27.222539+00:00
-- url     : https://prove2.me/theorems/530622ea-620b-440d-afd8-530df9fd4562
-- title:
--   Source Normal Closure
-- statement:
--   Definitions and structural lemmas for Source Normal Closure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosure.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceGaloisBaseFieldEmbedding (m : ℕ) :
    GaloisBaseField →ₐ[F256] SourceField m :=
  (IsScalarTower.toAlgHom F256 (RatFunc F256) (SourceField m)).comp
    (IntermediateField.adjoin F256
      ({galoisBaseZ} : Set (RatFunc F256))).val
noncomputable instance sourceGaloisBaseFieldSeedFiniteDimensional (m : ℕ) :
    FiniteDimensional GaloisBaseField (SourceField m) :=
  FiniteDimensional.trans GaloisBaseField (RatFunc F256) (SourceField m)
noncomputable instance sourceGaloisBaseFieldSeedSeparable (m : ℕ) :
    Algebra.IsSeparable GaloisBaseField (SourceField m) :=
  Algebra.IsSeparable.trans GaloisBaseField (RatFunc F256) (SourceField m)
abbrev SourceGaloisClosureAmbient : Type :=
  SeparableClosure GaloisBaseField
noncomputable instance sourceGaloisClosureAmbientAlgebra :
    Algebra GaloisBaseField SourceGaloisClosureAmbient :=
  (separableClosure GaloisBaseField
    (AlgebraicClosure GaloisBaseField)).toSubalgebra.algebra'
noncomputable instance (priority := 2000) sourceGaloisClosureAmbientSMul :
    SMul GaloisBaseField SourceGaloisClosureAmbient :=
  sourceGaloisClosureAmbientAlgebra.toSMul
noncomputable instance (priority := 2000) sourceGaloisClosureAmbientModule :
    Module GaloisBaseField SourceGaloisClosureAmbient :=
  @Algebra.toModule GaloisBaseField SourceGaloisClosureAmbient _ _
    sourceGaloisClosureAmbientAlgebra
noncomputable def sourceGaloisSeedSeparableEmbedding (m : ℕ) :
    SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient :=
  IsSepClosed.lift
noncomputable instance sourceGaloisSeedAmbientEmbeddingNonempty (m : ℕ) :
    Nonempty (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient) :=
  ⟨sourceGaloisSeedSeparableEmbedding m⟩
noncomputable instance sourceGaloisSeedAmbientAlgebra (m : ℕ) :
    Algebra (SourceField m) SourceGaloisClosureAmbient :=
  (sourceGaloisSeedSeparableEmbedding m).toRingHom.toAlgebra
noncomputable instance sourceGaloisSeedAmbientScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (SourceField m)
      SourceGaloisClosureAmbient :=
  IsScalarTower.of_algebraMap_eq'
    (sourceGaloisSeedSeparableEmbedding m).comp_algebraMap.symm
abbrev SourceGaloisClosureField (m : ℕ) : Type :=
  IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient
noncomputable instance sourceGaloisClosureFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField m) :=
  (IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient).toSubalgebra.algebra'
noncomputable instance (priority := 2000) sourceGaloisClosureFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisClosureFieldAlgebra m).toSMul
noncomputable instance (priority := 2000) sourceGaloisClosureFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureFieldAlgebra m)
noncomputable instance sourceGaloisClosureFieldFiniteDimensional (m : ℕ) :
    FiniteDimensional GaloisBaseField (SourceGaloisClosureField m) :=
  normalClosure.is_finiteDimensional GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient
noncomputable instance sourceGaloisClosureFieldIsNormalClosure (m : ℕ) :
    IsNormalClosure GaloisBaseField (SourceField m)
      (SourceGaloisClosureField m) :=
  isNormalClosure_normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient
noncomputable instance sourceGaloisClosureFieldIsGalois (m : ℕ) :
    IsGalois GaloisBaseField (SourceGaloisClosureField m) :=
  IsGalois.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient
noncomputable def sourceGaloisSeedToClosure (m : ℕ) :
    SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m :=
  IsScalarTower.toAlgHom GaloisBaseField (SourceField m)
    (SourceGaloisClosureField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


