-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
-- name    : QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:58:07.148215+00:00
-- url     : https://prove2.me/theorems/679b190c-289b-4f52-849f-498587e8b9d0
-- title:
--   Quadratic Tower
-- statement:
--   Definitions and structural lemmas for Quadratic Tower, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierAbovePlace_order_coordinate

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
structure QuadraticArtinSchreierTowerLevelData
    (K : Type u) [Field K] [Algebra F256 K] where
  carrier : Type u
  [field : _root_.Field carrier]
  [constantAlgebra : Algebra F256 carrier]
  [baseAlgebra : Algebra K carrier]
  [constantTower : IsScalarTower F256 K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [separable : Algebra.IsSeparable K carrier]
  place : GlobalPlace F256 carrier
  coordinate : carrier
  coordinate_order : place.order coordinate = -1
@[reducible] noncomputable def quadraticArtinSchreierTowerBaseData
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierTowerLevelData K where
  carrier := K
  field := inferInstance
  constantAlgebra := inferInstance
  baseAlgebra := inferInstance
  constantTower := inferInstance
  finiteDimensional := inferInstance
  separable := inferInstance
  place := P
  coordinate := a
  coordinate_order := ha
@[reducible] noncomputable def quadraticArtinSchreierTowerSuccessorData
    (data : QuadraticArtinSchreierTowerLevelData K) :
    QuadraticArtinSchreierTowerLevelData K := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra K data.carrier := data.baseAlgebra
  letI : IsScalarTower F256 K data.carrier := data.constantTower
  letI : FiniteDimensional K data.carrier := data.finiteDimensional
  letI : Algebra.IsSeparable K data.carrier := data.separable
  let L := QuadraticArtinSchreierField
    data.place data.coordinate data.coordinate_order
  letI : FiniteDimensional K L :=
    FiniteDimensional.trans K data.carrier L
  letI : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.trans K data.carrier L
  exact
    { carrier := L
      field := inferInstance
      constantAlgebra := inferInstance
      baseAlgebra := inferInstance
      constantTower := inferInstance
      finiteDimensional := inferInstance
      separable := inferInstance
      place := quadraticArtinSchreierAbovePlace
        data.place data.coordinate data.coordinate_order
      coordinate := quadraticArtinSchreierCoordinate
        data.place data.coordinate data.coordinate_order
      coordinate_order :=
        quadraticArtinSchreierAbovePlace_order_coordinate
          data.place data.coordinate data.coordinate_order }
@[reducible] noncomputable def quadraticArtinSchreierTowerLevelData
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    ℕ → QuadraticArtinSchreierTowerLevelData K
  | 0 => quadraticArtinSchreierTowerBaseData P a ha
  | i + 1 => quadraticArtinSchreierTowerSuccessorData
      (quadraticArtinSchreierTowerLevelData P a ha i)
abbrev QuadraticArtinSchreierTowerField
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) : Type u :=
  (quadraticArtinSchreierTowerLevelData P a ha i).carrier
noncomputable instance quadraticArtinSchreierTowerFieldField
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    _root_.Field (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).field
noncomputable instance quadraticArtinSchreierTowerFieldConstantAlgebra
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra F256 (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).constantAlgebra
noncomputable instance quadraticArtinSchreierTowerFieldBaseAlgebra
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).baseAlgebra
noncomputable instance quadraticArtinSchreierTowerFieldConstantTower
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    IsScalarTower F256 K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).constantTower
noncomputable instance quadraticArtinSchreierTowerFieldFiniteDimensional
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    FiniteDimensional K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).finiteDimensional
noncomputable instance quadraticArtinSchreierTowerFieldSeparable
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra.IsSeparable K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).separable
noncomputable def quadraticArtinSchreierTowerPlace
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    GlobalPlace F256 (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).place
noncomputable def quadraticArtinSchreierTowerCoordinate
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    QuadraticArtinSchreierTowerField P a ha i :=
  (quadraticArtinSchreierTowerLevelData P a ha i).coordinate
theorem quadraticArtinSchreierTowerCoordinate_order
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    (quadraticArtinSchreierTowerPlace P a ha i).order
      (quadraticArtinSchreierTowerCoordinate P a ha i) = -1 :=
  (quadraticArtinSchreierTowerLevelData P a ha i).coordinate_order
noncomputable def quadraticArtinSchreierTowerEmbedding
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    QuadraticArtinSchreierTowerField P a ha i →ₐ[F256]
      QuadraticArtinSchreierTowerField P a ha (i + 1) :=
  quadraticArtinSchreierEmbedding
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


