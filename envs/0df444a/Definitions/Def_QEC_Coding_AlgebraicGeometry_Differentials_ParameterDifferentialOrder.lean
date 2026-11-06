-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:30.461196+00:00
-- url     : https://prove2.me/theorems/714f7019-e13c-4642-b914-6e919c2cced3
-- title:
--   Parameter Differential Order
-- statement:
--   Definitions and structural lemmas for Parameter Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
theorem logarithmicDifferential_ne_zero_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    Differential.logarithmicDifferential (k := k) f ≠ 0 := by
  intro hz
  have h := Differential.simplePoleResidue_logarithmicDifferential P f hf
  have hzero : Differential.logarithmicDifferentialAtSimplePole P f hf = 0 := Subtype.ext hz
  rw [hzero, map_zero] at h
  rcases horder with horder | horder <;> rw [horder] at h <;> norm_num at h
variable {L : Type*} [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower (RatFunc k) K L]
end
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential


