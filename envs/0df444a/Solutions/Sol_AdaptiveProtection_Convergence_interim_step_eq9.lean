-- Prove2me | solution 1 for AdaptiveProtection.Convergence.interim_step_eq9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:03:15.650148+00:00
-- url     : https://prove2.me/submissions/f9dfabb0-eb6d-4030-86ea-713eb2809533

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace Aux_APInterim
open AdaptiveProtection.Convergence

lemma f_pos (k : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i)
    (hfpos : 0 < f (k + 1)) : ∀ n j, j + n = k + 1 → 1 ≤ j → 0 < f j := by
  intro n
  induction n with
  | zero => intro j hj _; simp at hj; subst hj; exact hfpos
  | succ n ih =>
    intro j hj h1
    exact (ih (j + 1) (by omega) (by omega)).trans (hf j h1 (by omega))

lemma fill_ae (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (θ : ℕ → ℝ) (i : ℕ)
    (hlt : θ (i + 1) < θ i) (hi : 1 ≤ i) (hnn : ∀ᵐ t ∂(ν (i + 1)), 0 ≤ t) :
    fillEvent θ i =ᵐ[flightLaw ν] fillEvent θ (i + 1) := by
  have hae : ∀ᵐ x ∂(flightLaw ν), 0 ≤ x (i + 1) := by
    have hmap : (flightLaw ν).map (fun x => x (i + 1)) = ν (i + 1) :=
      Measure.infinitePi_map_eval ν (i + 1)
    rw [← hmap] at hnn
    exact ae_of_ae_map (measurable_pi_apply (i + 1)).aemeasurable hnn
  rw [Filter.eventuallyEq_set]
  filter_upwards [hae] with x hx
  simp only [fillEvent, NestedSeatAlloc.ProbCond.nestEvent, Set.mem_setOf_eq, Finset.mem_Icc]
  constructor
  · intro h j hj
    rcases Nat.lt_or_ge j (i + 1) with hji | hji
    · exact h j ⟨hj.1, by omega⟩
    · have hj' : j = i + 1 := by omega
      subst hj'
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := h i ⟨hi, le_rfl⟩
      linarith
  · intro h j hj
    exact h j ⟨hj.1, by omega⟩

end Aux_APInterim

open AdaptiveProtection.Convergence Aux_APInterim in
theorem solution
    (k : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i) (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (θstar : ℕ → ℝ)
    (hopt : ∀ i, 1 ≤ i → i ≤ k → (flightLaw ν).real (fillEvent θstar i) = ratio f (i + 1))
    (i : ℕ) (hi : 1 ≤ i) (hik : i + 1 ≤ k) (hIH : interim θstar i = θstar i) :
    interim θstar (i + 1) = θstar (i + 1) := by
  have hle : θstar i ≤ θstar (i + 1) := by
    by_contra hcon
    push Not at hcon
    have hae := fill_ae ν θstar i hcon hi (hnonneg (i + 1) (by omega) (by omega))
    have h1 := hopt i hi (by omega)
    have h2 := hopt (i + 1) (by omega) hik
    rw [measureReal_congr hae, h2] at h1
    have hf1 : 0 < f 1 := f_pos k f hf hfpos k 1 (by omega) le_rfl
    have h3 := hf (i + 1) (by omega) hik
    unfold ratio at h1
    rw [div_left_inj' hf1.ne'] at h1
    linarith
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.lt_or_ge j (i + 1) with hji | hji
    · have : θstar j ≤ interim θstar i :=
        Finset.le_sup' θstar (by rw [Finset.mem_Icc]; omega)
      rw [hIH] at this
      linarith
    · have : j = i + 1 := by omega
      rw [this]
  · exact Finset.le_sup' θstar (by rw [Finset.mem_Icc]; omega)
