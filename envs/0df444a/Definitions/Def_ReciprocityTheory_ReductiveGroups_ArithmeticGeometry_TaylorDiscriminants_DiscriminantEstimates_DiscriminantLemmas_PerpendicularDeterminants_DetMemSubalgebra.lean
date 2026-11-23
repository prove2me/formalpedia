-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:10.013396+00:00
-- url     : https://prove2.me/theorems/59fbd907-676e-42b8-b5a7-e17b4750b549
-- title:
--   Det Mem Subalgebra
-- statement:
--   Definitions and structural lemmas for Det Mem Subalgebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/PerpendicularDeterminants/DetMemSubalgebra.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives
open ReciprocityTheory.ChartRestriction.G.TB MvPolynomial
variable {R : Type} [CommRing R] {p q n : ℕ}
def ySide (e : Fin p → Fin n → R) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {B | (∀ j, pderiv (Sum.inl j) B = 0) ∧
    (∀ j j', pderiv (Sum.inl j') (pderiv (Sum.inr j) B) = 0) ∧
    (∀ b', ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B = 0)}
  mul_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA1, hB1, hA2, hB2]
    · have : ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) (A * B)
          = (∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) A) * B
            + A * ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA3, hB3]; ring
  add_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA2, hB2]
    · simp only [map_add, mul_add, Finset.sum_add_distrib, hA3, hB3, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]
def xSide (e : Fin p → Fin n → R) (a : Fin p) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {A | (∀ j, pderiv (Sum.inr j) A = 0) ∧
    ∀ B ∈ ySide e b, ∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B = 0}
  mul_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · have : ∑ k, pderiv (Sum.inl (a, k)) (A * A') * pderiv (Sum.inr (b, k)) B
          = A' * (∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B)
            + A * ∑ k, pderiv (Sum.inl (a, k)) A' * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA2 B hB, hA'2 B hB]; ring
  add_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · simp only [map_add, add_mul, Finset.sum_add_distrib, hA2 B hB, hA'2 B hB, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun B _ => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]
end PI.UnitaryGroupMassFormula.FormPartialDerivatives


