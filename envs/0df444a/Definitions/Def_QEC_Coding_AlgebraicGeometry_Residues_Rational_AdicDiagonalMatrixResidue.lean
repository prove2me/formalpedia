-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:37:14.465198+00:00
-- url     : https://prove2.me/theorems/9141e877-4eeb-4b3a-a777-e16f3ba05e6a
-- title:
--   Adic Diagonal Matrix Residue
-- statement:
--   Definitions and structural lemmas for Adic Diagonal Matrix Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
variable {k : Type*} [Field k]
noncomputable def rationalDiagonalMatrixInverse
    {n : Type*} [DecidableEq n] (a : n → k[X]) :
    Matrix n n (RatFunc k) :=
  Matrix.diagonal fun i => (algebraMap k[X] (RatFunc k) (a i))⁻¹
namespace Differential
open FunctionFieldDifferential
variable [Finite k]
noncomputable def rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  ∑ i, rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    p (R i i) (a i) (ha i)
end Differential
end QEC.Coding.AlgebraicGeometry


