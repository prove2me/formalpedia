-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:36:11.375608+00:00
-- url     : https://prove2.me/theorems/2aff25be-3a5d-45d0-b536-f3469d78ba66
-- title:
--   Adic Polynomial Logarithmic Residue
-- statement:
--   Definitions and structural lemmas for Adic Polynomial Logarithmic Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
end GlobalPlace
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
noncomputable def rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p r •
    logarithmicDifferentialAtSimplePole
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (algebraMap k[X] (RatFunc k) a)
      (RatFunc.algebraMap_ne_zero ha)
end Differential
end QEC.Coding.AlgebraicGeometry


