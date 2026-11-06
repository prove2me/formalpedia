-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
-- name    : QEC_Coding_AlgebraicGeometry_Places_AffineResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:12:39.155507+00:00
-- url     : https://prove2.me/theorems/dc24bab6-768a-4660-99bc-002fd6f0554d
-- title:
--   Affine Residue
-- statement:
--   Definitions and structural lemmas for Affine Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
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
noncomputable def constantsToResidue (P : carrier k F) :
    k →+* residueField k F P :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)).comp
    ((algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F)).comp Polynomial.C)
@[reducible] noncomputable def residueAlgebra (P : carrier k F) :
    Algebra k (residueField k F P) :=
  (constantsToResidue k F P).toAlgebra
end AffinePlace
end QEC.Coding.AlgebraicGeometry


