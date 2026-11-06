-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:45:38.416769+00:00
-- url     : https://prove2.me/theorems/4d7759fa-72a6-405a-818d-ac2b2648ac88
-- title:
--   Valuation Bound
-- statement:
--   Definitions and structural lemmas for Valuation Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/ValuationBound.lean

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
namespace ValuationBound
variable {k F P : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
def space (valuations : P → Valuation F ℤᵐ⁰) (G : Divisor P) : Submodule k F where
  carrier := { f | ∀ place, valuations place f ≤ WithZero.exp (G place) }
  zero_mem' := by
    intro place
    simp
  add_mem' hf hg := by
    intro place
    exact (valuations place).map_add_le (hf place) (hg place)
  smul_mem' c f hf := by
    intro place
    by_cases hc : c = 0
    · subst c
      simp
    · rw [Algebra.smul_def, (valuations place).map_mul,
        FiniteField.valuation_algebraMap_eq_one (valuations place) c hc, one_mul]
      exact hf place
end ValuationBound
end QEC.Coding.AlgebraicGeometry


