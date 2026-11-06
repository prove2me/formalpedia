-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:52:56.944184+00:00
-- url     : https://prove2.me/theorems/eafe44bb-d806-4586-8da4-a2f2285551b6
-- title:
--   Prime Algebra Frobenius
-- statement:
--   Definitions and structural lemmas for Prime Algebra Frobenius, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]
lemma power_add (x y : R) : (x + y)^p = x^p + y^p := by
  classical
  rcases subsingleton_or_nontrivial R with h | h
  · have := h
    exact Subsingleton.elim _ _
  · have := h
    let : CharP R p :=
      charP_of_injective_ringHom (algebraMap (ZMod p) R).injective p
    simpa only [frobenius_def] using (frobenius R p).map_add x y
def primeAlgebraFrobenius : R →+* R where
  toFun x := x^p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' := power_add p R
end
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius


