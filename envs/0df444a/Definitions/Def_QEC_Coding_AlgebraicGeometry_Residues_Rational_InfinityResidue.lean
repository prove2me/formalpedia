-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:17:59.854197+00:00
-- url     : https://prove2.me/theorems/715eaff2-39e8-45f8-bb03-5079028f22b2
-- title:
--   Infinity Residue
-- statement:
--   Definitions and structural lemmas for Infinity Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinityResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


