-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:52.769036+00:00
-- url     : https://prove2.me/theorems/215fdc6e-0826-4e80-ba74-222d11d103a4
-- title:
--   Adele Effective Increment
-- statement:
--   Definitions and structural lemmas for Adele Effective Increment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleEffectiveIncrement.lean

import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
local instance globalAdeleFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _
attribute [local instance] globalAdeleFilterAddCommGroup
local instance globalAdeleFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _
attribute [local instance] globalAdeleFilterModule
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


