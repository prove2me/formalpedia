-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:12:45.732569+00:00
-- url     : https://prove2.me/theorems/fe82b76e-ca18-4b96-986e-699d06ff22c3
-- title:
--   Source Galois WZero Ramification
-- statement:
--   Definitions and structural lemmas for Source Galois WZero Ramification, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWZeroRamification.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureFieldAlgebra (m + 1)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureBaseSMulPinned (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  (sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned m).toSMul
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseSMulPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureBaseModulePinned (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField (m + 1)) _ _
    (sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned m)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseModulePinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned (m : ℕ) :
    Algebra F256 (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureConstantAlgebra (m + 1)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureConstantSMulPinned (m : ℕ) :
    SMul F256 (SourceGaloisClosureField (m + 1)) :=
  (sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned m).toSMul
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantSMulPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureConstantModulePinned (m : ℕ) :
    Module F256 (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule F256 (SourceGaloisClosureField (m + 1)) _ _
    (sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned m)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantModulePinned
noncomputable local instance sourceGaloisWZeroRamification_sourceZeroClosureConstantBaseTowerPinned
    (m : ℕ) : IsScalarTower F256 GaloisBaseField
      (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureConstantBaseScalarTower (m + 1)
attribute [local instance] sourceGaloisWZeroRamification_sourceZeroClosureConstantBaseTowerPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned (m : ℕ) :
    Algebra (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureRatFuncAlgebra (m + 1)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureRatFuncSMulPinned (m : ℕ) :
    SMul (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  (sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned m).toSMul
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncSMulPinned
noncomputable local instance (priority := 4000)
    sourceGaloisWZeroRamification_sourceZeroClosureRatFuncModulePinned (m : ℕ) :
    Module (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField (m + 1)) _ _
    (sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned m)
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncModulePinned
noncomputable local instance sourceGaloisWZeroRamification_sourceZeroClosureRatFuncTowerPinned
    (m : ℕ) : IsScalarTower F256 (RatFunc F256)
      (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureRatFuncScalarTower (m + 1)
attribute [local instance] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncTowerPinned
noncomputable def sourceGaloisWZeroRamification_sourceFirstLevelEmbedding :
    (m : ℕ) → SourceField 1 →ₐ[F256] SourceField (m + 1)
  | 0 => AlgHom.id F256 (SourceField 1)
  | m + 1 =>
      (sourceRecursionEmbedding (m + 1)).comp
        (sourceGaloisWZeroRamification_sourceFirstLevelEmbedding m)
noncomputable def sourceGaloisWZeroRamification_sourceFirstLevelToClosure (m : ℕ) :
    SourceField 1 →ₐ[F256] SourceGaloisClosureField (m + 1) :=
  ((sourceGaloisSeedToClosure (m + 1)).restrictScalars F256).comp
    (sourceGaloisWZeroRamification_sourceFirstLevelEmbedding m)
noncomputable def sourceGaloisWZeroRamification_sourceGaloisFirstSuccessorCoordinate (m : ℕ) :
    SourceGaloisClosureField (m + 1) :=
  sourceGaloisWZeroRamification_sourceFirstLevelToClosure m (sourceDistinguishedCoordinate 1)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


