-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_CanonicalCorrection
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_CanonicalCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:26:17.723315+00:00
-- url     : https://prove2.me/theorems/caf43af9-95b2-46e1-8c86-c6c70d65e9e3
-- title:
--   Canonical Correction
-- statement:
--   Definitions and structural lemmas for Canonical Correction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/CanonicalCorrection.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
variable [Algebra (Polynomial k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry


