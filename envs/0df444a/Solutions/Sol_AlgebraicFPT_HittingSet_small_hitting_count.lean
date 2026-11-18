-- Prove2me | solution 1 for AlgebraicFPT.HittingSet.small_hitting_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:11:53.21184+00:00
-- url     : https://prove2.me/submissions/d35334b4-645a-458e-b9fe-f31d01543f48

import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets

set_option autoImplicit false
open scoped BigOperators
namespace AlgebraicFPT.HittingSet
noncomputable section
variable {n : ℕ}

lemma hitting_mono {E : Finset (Finset (Fin n))} {C D : Finset (Fin n)}
    (h : IsHitting E C) (hCD : C ⊆ D) : IsHitting E D := by
  intro e he
  obtain ⟨i, hi⟩ := h e he
  exact ⟨i, Finset.mem_inter.mpr ⟨hCD (Finset.mem_inter.mp hi).1, (Finset.mem_inter.mp hi).2⟩⟩

lemma minimal_empty_iff (C : Finset (Fin n)) : IsMinimalHitting ∅ C ↔ C = ∅ := by
  constructor
  · intro h
    exact (h.2 ∅ (Finset.empty_subset _) (by simp [IsHitting])).symm
  · rintro rfl
    exact ⟨by simp [IsHitting], fun D hD _ => Finset.subset_empty.mp hD⟩

lemma erase_minimal {E : Finset (Finset (Fin n))} {C : Finset (Fin n)}
    (hC : IsMinimalHitting E C) (v : Fin n) (hv : v ∈ C) :
    IsMinimalHitting (E.filter (fun e => v ∉ e)) (C.erase v) := by
  classical
  have hhit : IsHitting (E.filter (fun e => v ∉ e)) (C.erase v) := by
    intro e he
    obtain ⟨heE, hve⟩ := Finset.mem_filter.mp he
    obtain ⟨i, hi⟩ := hC.1 e heE
    obtain ⟨hiC, hie⟩ := Finset.mem_inter.mp hi
    exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨by grind, hiC⟩, hie⟩⟩
  refine ⟨hhit, ?_⟩
  intro D hD hhitD
  have hhit' : IsHitting E (insert v D) := by
    intro e he
    by_cases hve : v ∈ e
    · exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hve⟩⟩
    · obtain ⟨i, hi⟩ := hhitD e (Finset.mem_filter.mpr ⟨he, hve⟩)
      exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hi).1,
        (Finset.mem_inter.mp hi).2⟩⟩
  have hh := hC.2 (insert v D) (Finset.insert_subset hv (hD.trans (Finset.erase_subset _ _))) hhit'
  apply Finset.Subset.antisymm hD
  intro i hi
  have hi' : i ∈ insert v D := hh.symm ▸ Finset.mem_of_mem_erase hi
  exact (Finset.mem_insert.mp hi').resolve_left (Finset.ne_of_mem_erase hi)

def smallFinset (E : Finset (Finset (Fin n))) (k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun C => IsMinimalHitting E C ∧ C.card ≤ k)

lemma mem_smallFinset (E : Finset (Finset (Fin n))) (k : ℕ) (C : Finset (Fin n)) :
    C ∈ smallFinset E k ↔ IsMinimalHitting E C ∧ C.card ≤ k := by
  classical
  simp [smallFinset]

lemma count_small (E : Finset (Finset (Fin n))) (k d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ E, e.card ≤ d) : (smallFinset E k).card ≤ d ^ k := by
  classical
  induction k generalizing E with
  | zero =>
    have hs : smallFinset E 0 ⊆ {∅} := by
      intro C hC
      have hc := ((mem_smallFinset E 0 C).mp hC).2
      simpa using Finset.card_eq_zero.mp (by omega : C.card = 0)
    simpa using Finset.card_le_card hs
  | succ k ih =>
    by_cases hEmpty : E = ∅
    · subst E
      have hs : smallFinset (∅ : Finset (Finset (Fin n))) (k + 1) ⊆ {∅} := by
        intro C hC
        simpa using (minimal_empty_iff C).mp ((mem_smallFinset _ _ _).mp hC).1
      have hc : (smallFinset (∅ : Finset (Finset (Fin n))) (k + 1)).card ≤ 1 := by
        simpa using Finset.card_le_card hs
      exact hc.trans (one_le_pow₀ hd)
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hs : smallFinset E (k + 1) ⊆
          e.biUnion (fun v => (smallFinset (E.filter (fun e => v ∉ e)) k).image (insert v)) := by
        intro C hC
        obtain ⟨hmin, hcard⟩ := (mem_smallFinset E (k+1) C).mp hC
        obtain ⟨v, hv⟩ := hmin.1 e he
        obtain ⟨hvC, hve⟩ := Finset.mem_inter.mp hv
        apply Finset.mem_biUnion.mpr
        refine ⟨v, hve, Finset.mem_image.mpr ⟨C.erase v, ?_, Finset.insert_erase hvC⟩⟩
        apply (mem_smallFinset _ _ _).mpr
        refine ⟨erase_minimal hmin v hvC, ?_⟩
        rw [Finset.card_erase_of_mem hvC]
        omega
      calc
        (smallFinset E (k + 1)).card ≤
            (e.biUnion (fun v => (smallFinset (E.filter (fun e => v ∉ e)) k).image (insert v))).card :=
          Finset.card_le_card hs
        _ ≤ ∑ v ∈ e, ((smallFinset (E.filter (fun e => v ∉ e)) k).image (insert v)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ v ∈ e, d ^ k := by
          apply Finset.sum_le_sum
          intro v hv
          apply (Finset.card_image_le).trans
          exact ih _ (fun e he => hE e (Finset.mem_filter.mp he).1)
        _ = e.card * d ^ k := by simp
        _ ≤ d * d ^ k := Nat.mul_le_mul_right _ (hE e he)
        _ = d ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

lemma small_encard_bound (E : Finset (Finset (Fin n))) (k d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ E, e.card ≤ d) : (smallHittingSets E k).encard ≤ (d ^ k : ℕ) := by
  classical
  have he : smallHittingSets E k = (smallFinset E k : Set (Finset (Fin n))) := by
    ext C
    exact (mem_smallFinset E k C).symm
  rw [he, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast count_small E k d hd hE

end
end AlgebraicFPT.HittingSet


theorem solution (n : ℕ) (E : Finset (Finset (Fin n))) (k d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ E, e.card ≤ d) :
    (AlgebraicFPT.HittingSet.smallHittingSets E k).encard ≤ (d ^ k : ℕ) := by
  exact AlgebraicFPT.HittingSet.small_encard_bound E k d hd hE
