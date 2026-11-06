-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:35:55.473465+00:00
-- url     : https://prove2.me/theorems/4c0ff9bb-7370-4849-a8ed-e0c7144a0d6a
-- title:
--   Logarithmic Residue
-- statement:
--   Definitions and structural lemmas for Logarithmic Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/LogarithmicResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


