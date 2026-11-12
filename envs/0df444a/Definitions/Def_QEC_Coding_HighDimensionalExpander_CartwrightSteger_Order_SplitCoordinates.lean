-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:21:10.811793+00:00
-- url     : https://prove2.me/theorems/3a15e988-5767-4520-a2e8-0a4dd5effb68
-- title:
--   Split Coordinates
-- statement:
--   Definitions and structural lemmas for Split Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_arithmetic_coordinate_of_cartwrightStegerOrder

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def cartwrightStegerOrderArithmeticCoordinate
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) : ArithmeticRing P :=
  Classical.choose
    (exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p)
noncomputable def cartwrightStegerOrderSplitCoordinate
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (cartwrightStegerOrderArithmeticCoordinate P r x p) •
      orderIndexCyclicBasisVector P r p
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


