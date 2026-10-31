-- Prove2me | solution 1 for AnyPriceShare.Bidding.proposition_3_7_proportional
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:49:39.337185+00:00
-- url     : https://prove2.me/submissions/03760974-4d83-45b2-af46-93146f329dd8

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

open AnyPriceShare.Bidding

namespace APSP37Sol

/-- Any feasible price vector bounds the AnyPrice share from above. -/
theorem anyPrice_le_of_prices {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ)
    (hβ : 0 ≤ β) (S : Finset (Fin m)) (X : ℝ) (p : Fin m → ℝ) (hp0 : ∀ j ∈ S, 0 ≤ p j)
    (hp1 : ∑ j ∈ S, p j = 1) (hX : ∀ T ⊆ S, ∑ j ∈ T, p j ≤ β → addVal u T ≤ X) :
    anyPrice β (addVal u) S ≤ X := by
  unfold anyPrice
  have hne : ∀ q : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      Nonempty {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, q.1 j ≤ β} :=
    fun q => ⟨⟨∅, Finset.empty_subset _, by simpa using hβ⟩⟩
  have hbdd : ∀ q : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      BddAbove (Set.range fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, q.1 j ≤ β} =>
        addVal u T.1) := fun q => (Set.finite_range _).bddAbove
  refine ciInf_le_of_le ⟨0, ?_⟩ ⟨p, hp0, hp1⟩ ?_
  · rintro _ ⟨q, rfl⟩
    refine le_ciSup_of_le (hbdd q) ⟨∅, Finset.empty_subset _, by simpa using hβ⟩ ?_
    simp [addVal]
  · haveI := hne ⟨p, hp0, hp1⟩
    exact ciSup_le fun T => hX T.1 T.2.1 T.2.2

theorem anyPrice_empty {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) :
    anyPrice β w ∅ = 0 := by
  unfold anyPrice
  haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
      ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
  exact Real.iInf_of_isEmpty _

end APSP37Sol

open APSP37Sol in
theorem solution {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPrice β (addVal u) S ≤ proportional β u S := by
  classical
  have hU0 : 0 ≤ ∑ j ∈ S, u j := Finset.sum_nonneg fun j _ => hu j
  rcases hU0.lt_or_eq with hU | hU
  · -- prices proportional to values
    refine anyPrice_le_of_prices u hu β hβ.le S _ (fun j => u j / ∑ j ∈ S, u j)
      (fun j _ => div_nonneg (hu j) hU0) ?_ ?_
    · rw [← Finset.sum_div]; exact div_self hU.ne'
    · intro T hT hpT
      rw [← Finset.sum_div, div_le_iff₀ hU] at hpT
      simpa [addVal, proportional] using hpT
  · -- all values on `S` vanish
    have hz : ∀ j ∈ S, u j = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hu j).1 hU.symm
    rcases S.eq_empty_or_nonempty with hS | ⟨j0, hj0⟩
    · subst hS; simp [anyPrice_empty, proportional]
    · refine anyPrice_le_of_prices u hu β hβ.le S _ (fun j => if j = j0 then 1 else 0)
        (fun j _ => by split_ifs <;> norm_num) (by simp [hj0]) ?_
      intro T hT _
      have : addVal u T = 0 := Finset.sum_eq_zero fun j hj => hz j (hT hj)
      rw [this, proportional, ← hU]; simp
