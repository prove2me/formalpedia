-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Recursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:06:57.168232+00:00
-- url     : https://prove2.me/theorems/4a9444d2-d4be-4e91-8fbb-1769fb003c1c
-- title:
--   Recursion
-- statement:
--   Definitions and structural lemmas for Recursion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Recursion.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAbovePlace_order_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
structure LevelData where
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
@[reducible] noncomputable def baseLevelData : LevelData where
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
@[reducible] noncomputable def successorLevelData
    (data : LevelData) : LevelData := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra (RatFunc F256) data.carrier := data.ratFuncAlgebra
  letI : IsScalarTower F256 (RatFunc F256) data.carrier := data.constantTower
  letI : FiniteDimensional (RatFunc F256) data.carrier := data.functionField
  letI : Algebra.IsSeparable (RatFunc F256) data.carrier := data.separable
  let L := StepField data.place data.coordinate data.coordinate_order
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
      place := stepAbovePlace data.place data.coordinate data.coordinate_order
      coordinate :=
        stepDistinguishedCoordinate data.place data.coordinate data.coordinate_order
      coordinate_order :=
        stepAbovePlace_order_stepDistinguishedCoordinate
          data.place data.coordinate data.coordinate_order }
@[reducible] noncomputable def levelData : ℕ → LevelData
  | 0 => baseLevelData
  | n + 1 => successorLevelData (levelData n)
abbrev Field (i : ℕ) : Type := (levelData i).carrier
noncomputable instance fieldField (i : ℕ) : _root_.Field (Field i) :=
  (levelData i).field
noncomputable instance fieldConstantAlgebra (i : ℕ) : Algebra F256 (Field i) :=
  (levelData i).constantAlgebra
noncomputable instance fieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (Field i) :=
  (levelData i).ratFuncAlgebra
noncomputable instance fieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (Field i) :=
  (levelData i).constantTower
noncomputable instance fieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field i) :=
  (levelData i).functionField
noncomputable instance fieldSuccessorFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field (i + 1)) :=
  (levelData (i + 1)).functionField
noncomputable instance fieldSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field i) :=
  (levelData i).separable
noncomputable instance fieldSuccessorSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field (i + 1)) :=
  (levelData (i + 1)).separable
noncomputable def distinguishedPlace (i : ℕ) : GlobalPlace F256 (Field i) :=
  (levelData i).place
noncomputable def distinguishedCoordinate (i : ℕ) : Field i :=
  (levelData i).coordinate
theorem distinguishedCoordinate_order (i : ℕ) :
    (distinguishedPlace i).order (distinguishedCoordinate i) = -1 :=
  (levelData i).coordinate_order
noncomputable def stepEmbedding (i : ℕ) : Field i →ₐ[F256] Field (i + 1) :=
  (stepFieldEmbedding (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)).restrictScalars F256
noncomputable def auxiliaryCoordinate (i : ℕ) : Field (i + 1) :=
  stepAuxiliaryCoordinate (distinguishedPlace i) (distinguishedCoordinate i)
    (distinguishedCoordinate_order i)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


