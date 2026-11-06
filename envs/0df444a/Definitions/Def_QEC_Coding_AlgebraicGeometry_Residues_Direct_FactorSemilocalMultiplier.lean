-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:36:14.038766+00:00
-- url     : https://prove2.me/theorems/6efc5737-710a-4b38-bc5d-a763fc90fd6d
-- title:
--   Factor Semilocal Multiplier
-- statement:
--   Definitions and structural lemmas for Factor Semilocal Multiplier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalMultiplier.lean

import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_e0603924bb_41 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier


