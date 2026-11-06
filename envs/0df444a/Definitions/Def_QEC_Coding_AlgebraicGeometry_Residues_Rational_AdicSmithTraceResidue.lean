-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:38:11.236245+00:00
-- url     : https://prove2.me/theorems/31d3890e-bc09-4472-b9a4-13ffa877010f
-- title:
--   Adic Smith Trace Residue
-- statement:
--   Definitions and structural lemmas for Adic Smith Trace Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
noncomputable def rationalAdicIdealResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (k[X] ⧸ p.asIdeal) ≃+* (rationalAdic p).residueField :=
  (Ideal.quotEquivOfEq (rationalAdic_asIdeal_eq_span p)).trans
    (rationalAdicResidueEquiv p)
end GlobalPlace
namespace Differential
variable {k : Type*} [Field k] [Finite k]
end Differential
end QEC.Coding.AlgebraicGeometry


