-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:59:47.681208+00:00
-- url     : https://prove2.me/theorems/c3f32a2d-3880-4871-b04f-7fe66822c6a3
-- title:
--   Projective Units
-- statement:
--   Definitions and structural lemmas for Projective Units, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/ProjectiveUnits.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def globalIntegralUnitGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.map (skewLaurentToGlobalMatrix P r).toMonoidHom
noncomputable def globalIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.ProjGenLinGroup.mk.comp (globalIntegralUnitGLHom P r)
noncomputable def globalConstantPGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.ProjGenLinGroup.mk.comp
    (Units.map (constantMatrixEmbedding P r).toMonoidHom)
noncomputable def globalCyclicGeneratorPGL
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  Matrix.ProjGenLinGroup.mk (cyclicGenerator P r)
noncomputable def GlobalIntegralCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) :=
  Subgroup.closure
    (Set.range (globalConstantPGLHom P r) ∪
      {globalCyclicGeneratorPGL P r})
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


