-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:40:05.914193+00:00
-- url     : https://prove2.me/theorems/c51519dd-ac02-42cd-9bcf-ffe559b31c61
-- title:
--   Direct Norm Count
-- statement:
--   Definitions and structural lemmas for Direct Norm Count, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectNormCount
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
abbrev directRingOfIntegers : Type _ := _root_.FunctionField.ringOfIntegers k F
noncomputable abbrev directBasePrime (P : AffinePlace.carrier k F) : Ideal k[X] :=
  P.asIdeal.under k[X]
local instance _p2m_local_instance_154c3067f1_22 : Module.IsTorsionFree k[X] (directRingOfIntegers k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectNormCount
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
end QEC.Coding.AlgebraicGeometry.AffinePlace


