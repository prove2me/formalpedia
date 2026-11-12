-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:35:48.599724+00:00
-- url     : https://prove2.me/theorems/98c1c7bd-9f27-4849-be6a-3cd4019d4b0d
-- title:
--   Apartment Completion
-- statement:
--   Definitions and structural lemmas for Apartment Completion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke
noncomputable def translatedRankThreeVertex1
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk (left *
    coordinateUniformizerCoweight (BaseField P) 3 0)
noncomputable def translatedRankThreeVertex2
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk ((left *
    coordinateUniformizerCoweight (BaseField P) 3 0) *
      coordinateUniformizerCoweight (BaseField P) 3 1)
noncomputable def translatedRankFourVertex1
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (left *
    coordinateUniformizerCoweight (BaseField P) 4 0)
noncomputable def translatedRankFourVertex2
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk ((left *
    coordinateUniformizerCoweight (BaseField P) 4 0) *
      coordinateUniformizerCoweight (BaseField P) 4 1)
noncomputable def translatedRankFourVertex3
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (((left *
    coordinateUniformizerCoweight (BaseField P) 4 0) *
      coordinateUniformizerCoweight (BaseField P) 4 1) *
        coordinateUniformizerCoweight (BaseField P) 4 2)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


