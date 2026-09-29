-- Prove2me | solution 1 for ArithmeticE.relation_basis_specializes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:38:37.624259+00:00
-- url     : https://prove2.me/submissions/0cbf931d-cd72-4b91-b5bd-d7bb4db4cd47

import Definitions.Def_beukersLiftingData
import Theorems.Thm_ArithmeticE_polynomial_relation_basis
open ArithmeticE Polynomial

namespace BeukersRelations
lemma specialize_independent {K : Type*} [Field K] {m r : ℕ}
    (C U : Fin r → Fin m → Polynomial K)
    (hU : ∀ j k, ∑ i, U j i * C k i = if j = k then 1 else 0)
    (ξ : K) : LinearIndependent K (fun j i => (C j i).eval ξ) := by
  classical
  have he : ∀ j k, ∑ i, (U j i).eval ξ * (C k i).eval ξ =
      if j = k then 1 else 0 := by
    intro j k
    simpa only [eval_finsetSum, eval_mul, apply_ite, eval_one, eval_zero] using
      congrArg (fun p : Polynomial K => p.eval ξ) (hU j k)
  rw [Fintype.linearIndependent_iff]
  intro d hd j
  have hd' : ∀ i, ∑ k, d k * (C k i).eval ξ = 0 := by
    intro i
    simpa using congrFun hd i
  calc
    d j = ∑ k, d k * (∑ i, (U j i).eval ξ * (C k i).eval ξ) := by simp [he]
    _ = ∑ i, (U j i).eval ξ * (∑ k, d k * (C k i).eval ξ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by simp [hd']
end BeukersRelations


theorem solution (m : ℕ) (f : Fin m → PowerSeries ℂ) :
    ∃ (r : ℕ) (C : Fin r → Fin m → Polynomial ℂ),
      (∀ j, ∑ i, (C j i : PowerSeries ℂ) * f i = 0) ∧
      (∀ p : Fin m → Polynomial ℂ, (∑ i, (p i : PowerSeries ℂ) * f i = 0) →
        ∃ b : Fin r → Polynomial ℂ, ∀ i, p i = ∑ j, b j * C j i) ∧
      (∀ ξ : ℂ, LinearIndependent ℂ (fun j i => (C j i).eval ξ)) := by
  obtain ⟨r, C, U, hC, hspan, hU⟩ := polynomial_relation_basis m f
  exact ⟨r, C, hC, hspan, BeukersRelations.specialize_independent C U hU⟩
#print axioms solution
