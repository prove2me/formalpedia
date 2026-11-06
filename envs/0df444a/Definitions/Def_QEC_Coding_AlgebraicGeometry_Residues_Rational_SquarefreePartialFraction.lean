-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:42:59.359241+00:00
-- url     : https://prove2.me/theorems/e5673433-6430-4b17-b069-dcfea96c18e8
-- title:
--   Squarefree Partial Fraction
-- statement:
--   Definitions and structural lemmas for Squarefree Partial Fraction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SquarefreePartialFraction.lean

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.PartialFractions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k]
end Differential
end QEC.Coding.AlgebraicGeometry


