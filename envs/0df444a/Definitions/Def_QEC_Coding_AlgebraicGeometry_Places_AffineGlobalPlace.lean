-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:09:30.670493+00:00
-- url     : https://prove2.me/theorems/76db8455-22e7-460a-a7be-86ae6e6b6984
-- title:
--   Affine Global Place
-- statement:
--   Definitions and structural lemmas for Affine Global Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
namespace AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable def constantsToFunctionField : k →+* F :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    ((algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F)).comp Polynomial.C)
@[reducible] noncomputable def constantAlgebra : Algebra k F :=
  (constantsToFunctionField k F).toAlgebra
noncomputable local instance _p2m_local_instance_439b1c180e_47 : Algebra k F := constantAlgebra k F
noncomputable def globalPlace (P : carrier k F) :
    @GlobalPlace k F _ _ _ (constantAlgebra k F) where
  valuation := valuation k F P
  normalized := P.valuation_surjective F
end AffinePlace
end QEC.Coding.AlgebraicGeometry


