-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:38:53.764855+00:00
-- url     : https://prove2.me/theorems/db1b87f5-7377-475a-9f43-7cc1dc19ed8a
-- title:
--   Normal Closure Divisor
-- statement:
--   Definitions and structural lemmas for Normal Closure Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
def f256MultiplicationCoefficient (i : ℕ) : ℤ :=
  (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) / 3
def f256MultiplicationDivisor (i : ℕ) :
    Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  f256MultiplicationCoefficient i • f256GarciaStichtenothDivisorA i
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


