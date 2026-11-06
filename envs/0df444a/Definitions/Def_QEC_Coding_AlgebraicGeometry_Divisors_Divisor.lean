-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_Divisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:09:48.332194+00:00
-- url     : https://prove2.me/theorems/4829fe2e-fdfe-4863-8623-bbe1c8e1493b
-- title:
--   Divisor
-- statement:
--   Definitions and structural lemmas for Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/Divisor.lean

import Mathlib.Data.Finsupp.Weight
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators
abbrev Divisor (P : Type*) := P →₀ ℤ
namespace Divisor
variable {P : Type*}
def support (D : Divisor P) : Finset P := Finsupp.support D
noncomputable def degreeHom (degreeOf : P → ℕ) : Divisor P →+ ℤ where
  toFun D := D.sum fun P coefficient => coefficient * (degreeOf P : ℤ)
  map_zero' := Finsupp.sum_zero_index
  map_add' D E := by
    change (D + E).sum (fun P coefficient => coefficient * (degreeOf P : ℤ)) =
      D.sum (fun P coefficient => coefficient * (degreeOf P : ℤ)) +
        E.sum (fun P coefficient => coefficient * (degreeOf P : ℤ))
    exact Finsupp.sum_add_index'
      (fun _ => by simp)
      (fun _ _ _ => by ring)
noncomputable def degree (degreeOf : P → ℕ) (D : Divisor P) : ℤ := degreeHom degreeOf D
def Nonnegative (D : Divisor P) : Prop := ∀ P, 0 ≤ D P
end Divisor
end QEC.Coding.AlgebraicGeometry


