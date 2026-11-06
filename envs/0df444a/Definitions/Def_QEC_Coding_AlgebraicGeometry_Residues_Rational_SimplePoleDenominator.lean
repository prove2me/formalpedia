-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:42:06.647249+00:00
-- url     : https://prove2.me/theorems/774de2b1-f663-4895-ba52-3cc3e40d191a
-- title:
--   Simple Pole Denominator
-- statement:
--   Definitions and structural lemmas for Simple Pole Denominator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
end Differential
end QEC.Coding.AlgebraicGeometry


