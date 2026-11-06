-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:39:10.274296+00:00
-- url     : https://prove2.me/theorems/3e29f525-c8be-4903-9285-dbdfc0137a36
-- title:
--   Adic Smith Matrix Residue
-- statement:
--   Definitions and structural lemmas for Adic Smith Matrix Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
namespace Differential
variable {k : Type*} [Field k] [Finite k]
noncomputable def rationalAdicSmithLogarithmicDifferentialAtSimplePole
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (g : N →ₗ[k[X]] N) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
      (LinearMap.toMatrix source source g) a ha +
    polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
      (LinearMap.toMatrix target target g * target.toMatrix source)
      (source.toMatrix target)
end Differential
end QEC.Coding.AlgebraicGeometry


