-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:33:22.609769+00:00
-- url     : https://prove2.me/theorems/392d8b91-b6ee-4c66-9cfa-931bc873f769
-- title:
--   Adic Polynomial Matrix Residue
-- statement:
--   Definitions and structural lemmas for Adic Polynomial Matrix Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialMatrixResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
noncomputable def polynomialMatrixLogarithmicTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (Pinv P : Matrix n n k[X]) : k[X] :=
  Matrix.trace (Pinv * entrywisePolynomialDerivative P)
noncomputable def polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
  Differential.rationalAdicPolynomialDifferentialAtSimplePole p
    (polynomialMatrixLogarithmicTrace Pinv P)
end QEC.Coding.AlgebraicGeometry


