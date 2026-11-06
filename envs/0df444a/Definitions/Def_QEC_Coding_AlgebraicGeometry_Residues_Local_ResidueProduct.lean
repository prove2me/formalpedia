-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:32:08.758807+00:00
-- url     : https://prove2.me/theorems/9ec0ff75-636e-429f-8774-cb8669268051
-- title:
--   Residue Product
-- statement:
--   Definitions and structural lemmas for Residue Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


