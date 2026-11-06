-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
-- name    : QEC_Coding_AlgebraicGeometry_Places_FullConstantField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:50:52.450568+00:00
-- url     : https://prove2.me/theorems/f8e8c734-e79e-4b51-83ba-60a75adc79c9
-- title:
--   Full Constant Field
-- statement:
--   Definitions and structural lemmas for Full Constant Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/FullConstantField.lean

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped RatFunc
class IsFullConstantField (k F : Type*) [Field k] [Field F] [Algebra k F] : Prop where
  /-- Algebraic elements of the function field come from the constant field. -/
  algebraic_mem : ∀ x : F, IsAlgebraic k x → ∃ c : k, x = algebraMap k F c
namespace IsFullConstantField
variable (k F : Type*) [Field k] [Field F] [Algebra k F] [IsFullConstantField k F]
end IsFullConstantField
instance ratFuncIsFullConstantField (k : Type*) [Field k] :
    IsFullConstantField k (RatFunc k) where
  algebraic_mem x hx := by
    by_contra h
    exact RatFunc.transcendental_of_ne_C x h hx
end QEC.Coding.AlgebraicGeometry


