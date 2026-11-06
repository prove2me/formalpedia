-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:21:30.521305+00:00
-- url     : https://prove2.me/theorems/45bcca15-4b5c-4807-89c9-3b6206c335f5
-- title:
--   Dimension
-- statement:
--   Definitions and structural lemmas for Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Dimension.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
noncomputable def riemannRochDimension (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (riemannRochSubmodule G)] : ℕ :=
  Module.finrank k (riemannRochSubmodule G)
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


