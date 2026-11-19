-- Prove2me | Definitions.Def_APFFinitePairing_form
-- name    : APFFinitePairing_form
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T08:01:58.215521+00:00
-- url     : https://prove2.me/theorems/863a5919-f47e-4349-803c-d7d9694a4fa4
-- title:
--   Finite-table bilinear form
-- statement:
--   # Finite-table bilinear form
--
--   A finite real table extends by a double sum to a bilinear form on formal row and column coefficient spaces.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
def APFFinitePairing.form (M : I → J → ℝ) : (I → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => ∑ i, ∑ j, a i * M i j * b j)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring)


