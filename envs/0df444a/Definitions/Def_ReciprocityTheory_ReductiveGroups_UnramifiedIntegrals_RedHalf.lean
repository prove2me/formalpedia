-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:47.527878+00:00
-- url     : https://prove2.me/theorems/d593d83e-9f64-48cc-9509-7c66c02fa35a
-- title:
--   Red Half
-- statement:
--   Definitions and structural lemmas for Red Half, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
namespace ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}
theorem IsHalfReps.notMem (h : IsHalfReps L α T) {P : ℂ} (hP : P ∈ T) : P ∉ L.lattice := by
  intro hPL
  apply (h.1 P hP).2
  rw [two_mul]
  exact add_mem hPL hPL
theorem IsHalfReps.kerReps (h : IsHalfReps L α T) :
    IsKerReps L α (T ∪ T.image (fun P => -P)) ∧ Disjoint T (T.image (fun P => -P)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact ⟨(h.1 P hP).1, h.notMem hP⟩
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨?_, ?_⟩
      · rw [mul_neg]; exact neg_mem (h.1 Q hQ).1
      · intro hn; exact h.notMem hQ (by simpa using neg_mem hn)
  · intro P hP Q hQ hPQ
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact h.2.1 P hP Q hQ (Or.inl hPQ)
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have e : P = Q' := h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))
      subst e
      exact absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      have h1 : P' + Q ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - Q) = P' + Q := by ring
        rwa [e] at this
      have e : P' = Q := h.2.1 P' hP' Q hQ (Or.inr h1)
      subst e
      exact absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have h1 : P' - Q' ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - -Q') = P' - Q' := by ring
        rwa [e] at this
      rw [h.2.1 P' hP' Q' hQ' (Or.inl h1)]
  · intro z hz hzL
    obtain ⟨P, hP, hzP | hzP⟩ := h.2.2 z hz hzL
    · exact ⟨P, Finset.mem_union_left _ hP, hzP⟩
    · exact ⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP'
    have h0 : P + Q ∈ L.lattice := by rw [← hQP]; simp
    have e : P = Q := h.2.1 P hP Q hQ (Or.inr h0)
    subst e
    exact (h.1 P hP).2 (by rw [two_mul]; exact h0)
theorem IsHalfReps.card (h : IsHalfReps L α T) (hα : α ≠ 0) (hs : MulStable L α) :
    2 * (T.card : ℝ) + 1 = Complex.normSq α := by
  have h1 := kerRepsCard L α _ hα hs h.kerReps.1
  rw [Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective] at h1
  rw [← h1]; push_cast; ring
end ReciprocityTheory.ChartRestriction.L1


