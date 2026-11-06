-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:38:35.938773+00:00
-- url     : https://prove2.me/theorems/eca836e3-a1f4-4b6f-b934-0204873650b5
-- title:
--   Place Increment Dimension
-- statement:
--   Definitions and structural lemmas for Place Increment Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrementDimension.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_le_add_placeDivisor

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
noncomputable def riemannRochPlaceIncrementEquiv
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochSubmodule G ≃ₗ[k] riemannRochPlaceIncrementSubmodule G P where
  toFun x :=
    ⟨⟨x.1, riemannRochSubmodule_le_add_placeDivisor G P x.property⟩, x.property⟩
  invFun x := ⟨x.1.1, x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


