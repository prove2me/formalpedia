-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:10:44.728435+00:00
-- url     : https://prove2.me/theorems/95f1adba-1541-4e5b-bd8f-ab5a3d71f779
-- title:
--   Adele Quotient
-- statement:
--   Definitions and structural lemmas for Adele Quotient, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleQuotientAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
local instance globalAdeleQuotientScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
namespace GlobalPlace
variable [IsFullConstantField k F]
local instance globalAdeleQuotientFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _
local instance globalAdeleQuotientFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _
def globalAdeleFilterAddDiagonal
    (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F)) :=
  globalAdeleFilter (k := k) (F := F) D +
    diagonalAdeleSubmodule (k := k) (F := F)
abbrev GlobalAdeleQuotient
    (D : Divisor (GlobalPlace k F)) :=
  GlobalAdele (k := k) (F := F) ⧸
    globalAdeleFilterAddDiagonal (k := k) (F := F) D
noncomputable def globalAdeleQuotientRank
    (D : Divisor (GlobalPlace k F)) : ℕ :=
  Module.finrank k (GlobalAdeleQuotient (k := k) (F := F) D)
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


