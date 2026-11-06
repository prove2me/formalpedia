-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:55:21.596464+00:00
-- url     : https://prove2.me/theorems/7e4c1e6e-4cef-4289-8c49-92fbb0600e59
-- title:
--   Source Recursion
-- statement:
--   Definitions and structural lemmas for Source Recursion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepAbovePlace_order_coordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
structure SourceLevelData where
  carrier : Type
  [field : _root_.Field carrier]
  [constantAlgebra : Algebra F256 carrier]
  [ratFuncAlgebra : Algebra (RatFunc F256) carrier]
  [constantTower : IsScalarTower F256 (RatFunc F256) carrier]
  [functionField : FiniteDimensional (RatFunc F256) carrier]
  [separable : Algebra.IsSeparable (RatFunc F256) carrier]
  place : GlobalPlace F256 carrier
  coordinate : carrier
  coordinate_order : place.order coordinate = -1
@[reducible] noncomputable def sourceBaseLevelData : SourceLevelData where
  carrier := RatFunc F256
  field := inferInstance
  constantAlgebra := inferInstance
  ratFuncAlgebra := inferInstance
  constantTower := inferInstance
  functionField := inferInstance
  separable := inferInstance
  place := GlobalPlace.rationalInfinity F256
  coordinate := RatFunc.X
  coordinate_order := by
    rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      F256 RatFunc.X RatFunc.X_ne_zero, RatFunc.intDegree_X]
@[reducible] noncomputable def sourceSuccessorLevelData
    (data : SourceLevelData) : SourceLevelData := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra (RatFunc F256) data.carrier := data.ratFuncAlgebra
  letI : IsScalarTower F256 (RatFunc F256) data.carrier := data.constantTower
  letI : FiniteDimensional (RatFunc F256) data.carrier := data.functionField
  letI : Algebra.IsSeparable (RatFunc F256) data.carrier := data.separable
  let L := SourceStepField data.place data.coordinate data.coordinate_order
  letI : FiniteDimensional (RatFunc F256) L :=
    FiniteDimensional.trans (RatFunc F256) data.carrier L
  letI : Algebra.IsSeparable (RatFunc F256) L :=
    Algebra.IsSeparable.trans (RatFunc F256) data.carrier L
  exact
    { carrier := L
      field := inferInstance
      constantAlgebra := inferInstance
      ratFuncAlgebra := inferInstance
      constantTower := inferInstance
      functionField := inferInstance
      separable := inferInstance
      place := sourceStepAbovePlace data.place data.coordinate data.coordinate_order
      coordinate := sourceStepCoordinate data.place data.coordinate data.coordinate_order
      coordinate_order :=
        sourceStepAbovePlace_order_coordinate
          data.place data.coordinate data.coordinate_order }
@[reducible] noncomputable def sourceLevelData : ℕ → SourceLevelData
  | 0 => sourceBaseLevelData
  | i + 1 => sourceSuccessorLevelData (sourceLevelData i)
abbrev SourceField (i : ℕ) : Type := (sourceLevelData i).carrier
noncomputable instance sourceFieldField (i : ℕ) :
    _root_.Field (SourceField i) :=
  (sourceLevelData i).field
noncomputable instance sourceFieldConstantAlgebra (i : ℕ) :
    Algebra F256 (SourceField i) :=
  (sourceLevelData i).constantAlgebra
noncomputable instance sourceFieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).ratFuncAlgebra
noncomputable instance sourceFieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).constantTower
noncomputable instance sourceFieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (SourceField i) :=
  (sourceLevelData i).functionField
noncomputable instance sourceFieldSuccessorFunctionField (i : ℕ) :
    _root_.FunctionField F256 (SourceField (i + 1)) :=
  (sourceLevelData (i + 1)).functionField
noncomputable instance sourceFieldSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (SourceField i) :=
  (sourceLevelData i).separable
noncomputable instance sourceFieldSuccessorSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (SourceField (i + 1)) :=
  (sourceLevelData (i + 1)).separable
noncomputable def sourceDistinguishedPlace (i : ℕ) :
    GlobalPlace F256 (SourceField i) :=
  (sourceLevelData i).place
noncomputable def sourceDistinguishedCoordinate (i : ℕ) : SourceField i :=
  (sourceLevelData i).coordinate
theorem sourceDistinguishedCoordinate_order (i : ℕ) :
    (sourceDistinguishedPlace i).order (sourceDistinguishedCoordinate i) = -1 :=
  (sourceLevelData i).coordinate_order
noncomputable def sourceRecursionEmbedding (i : ℕ) :
    SourceField i →ₐ[F256] SourceField (i + 1) :=
  sourceStepEmbedding (sourceDistinguishedPlace i)
    (sourceDistinguishedCoordinate i) (sourceDistinguishedCoordinate_order i)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


