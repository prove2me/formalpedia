-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:43:02.44824+00:00
-- url     : https://prove2.me/theorems/6b13821d-5cf8-4ff5-86d9-4e09580a52c0
-- title:
--   Simple Transitivity
-- statement:
--   Definitions and structural lemmas for Simple Transitivity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def orderUnitToGlobalPGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.ProjGenLinGroup.mk.comp (orderUnitToGlobalGL P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


