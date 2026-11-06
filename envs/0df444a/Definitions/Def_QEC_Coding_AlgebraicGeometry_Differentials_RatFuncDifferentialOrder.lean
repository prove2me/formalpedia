-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:34.100201+00:00
-- url     : https://prove2.me/theorems/8d46d8c9-a835-43d0-bd8e-c34f93c11fc0
-- title:
--   Rat Func Differential Order
-- statement:
--   Definitions and structural lemmas for Rat Func Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
theorem logarithmicDifferential_ne_zero_of_order_eq_one
    (P : GlobalPlace k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    logarithmicDifferential (k := k) (F := RatFunc k) f ≠ 0 := by
  intro hzero
  have hresidue := simplePoleResidue_logarithmicDifferential
    (k := k) (F := RatFunc k) P f hf
  have hsubtype :
      logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k) P f hf =
        0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero, horder] at hresidue
  norm_num at hresidue
end Differential
end QEC.Coding.AlgebraicGeometry


