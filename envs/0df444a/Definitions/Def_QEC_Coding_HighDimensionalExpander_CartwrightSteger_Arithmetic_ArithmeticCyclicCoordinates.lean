-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:51:45.343206+00:00
-- url     : https://prove2.me/theorems/54f85954-96e5-4067-9c23-2bc88d2948b9
-- title:
--   Arithmetic Cyclic Coordinates
-- statement:
--   Definitions and structural lemmas for Arithmetic Cyclic Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/ArithmeticCyclicCoordinates.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable instance arithmeticRingFunctionFieldAlgebra
    (P : BasePrime) : Algebra (ArithmeticRing P) (FunctionField P) :=
  (arithmeticRingToFunctionField P).toAlgebra
noncomputable instance arithmeticRingCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    Algebra (ArithmeticRing P) (CyclicAlgebra P r) where
  smul a x := (arithmeticRingToFunctionField P a) • x
  algebraMap := (algebraMap (FunctionField P) (CyclicAlgebra P r)).comp
    (arithmeticRingToFunctionField P)
  commutes' a x := Algebra.commutes
    (arithmeticRingToFunctionField P a) x
  smul_def' a x := by
    change (arithmeticRingToFunctionField P a) • x =
      algebraMap (FunctionField P) (CyclicAlgebra P r)
        (arithmeticRingToFunctionField P a) * x
    rw [Algebra.smul_def]
noncomputable instance arithmeticFunctionFieldCyclicTower
    (P : BasePrime) (r : Rank) :
    IsScalarTower (ArithmeticRing P) (FunctionField P) (CyclicAlgebra P r) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) :
    Submodule (ArithmeticRing P) (CyclicAlgebra P r) :=
  Submodule.span (ArithmeticRing P)
    (Set.range (functionFieldCyclicBasisVector P r))
noncomputable def arithmeticOnePlusY (P : BasePrime) : ArithmeticRing P :=
  algebraMap (PolynomialRing P) (ArithmeticRing P) (1 + Polynomial.X)
noncomputable def arithmeticOnePlusYInv (P : BasePrime) : ArithmeticRing P :=
  algebraMap (PolynomialRing P) (ArithmeticRing P) Polynomial.X *
    IsLocalization.Away.invSelf
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


