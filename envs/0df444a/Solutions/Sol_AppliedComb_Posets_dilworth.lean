-- Prove2me | solution 1 for AppliedComb.Posets.dilworth
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:48:25.592119+00:00
-- url     : https://prove2.me/submissions/07ba55c1-4786-4e5c-9222-2ff5d57a98b7

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_AppliedComb_Posets_chainPartition



namespace AppliedComb.Posets

theorem dil_claim {α : Type*} [PartialOrder α] (S : Finset α) :
    ∀ n : ℕ, (∀ A ⊆ S, IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ n) →
    ∃ c : α → ℕ, (∀ x ∈ S, c x < n) ∧ ∀ x ∈ S, ∀ y ∈ S, c x = c y → x ≤ y ∨ y ≤ x := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  intro n hn
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨m, hm⟩ := S.exists_maximal hne
  have hmS : m ∈ S := hm.prop
  have hmax : ∀ y ∈ S, m ≤ y → y = m := fun y hy h => le_antisymm (hm.2 hy h) h
  set S' := S.erase m with hS'
  have hS'S : S' ⊆ S := Finset.erase_subset _ _
  set w' := (S'.powerset.filter (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α))).sup Finset.card
    with hw'
  have hw'le : ∀ A ⊆ S', IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ w' := fun A hA hac =>
    Finset.le_sup (f := Finset.card) (by simp [hA, hac])
  have hw'ex : ∃ A0, A0 ⊆ S' ∧ IsAntichain (· ≤ ·) (A0 : Set α) ∧ A0.card = w' := by
    obtain ⟨A0, hA0, he⟩ := Finset.exists_mem_eq_sup
      (S'.powerset.filter (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α)))
      ⟨∅, by simp⟩ Finset.card
    simp only [Finset.mem_filter, Finset.mem_powerset] at hA0
    exact ⟨A0, hA0.1, hA0.2, he.symm⟩
  obtain ⟨A0, hA0S, hA0ac, hA0c⟩ := hw'ex
  have hw'n : w' ≤ n := hA0c ▸ hn A0 (hA0S.trans hS'S) hA0ac
  obtain ⟨c', hc'lt, hc'ch⟩ := ih S' (Finset.erase_ssubset hmS) w' hw'le
  have hmeet : ∀ B, B ⊆ S' → IsAntichain (· ≤ ·) (B : Set α) → B.card = w' →
      ∀ i < w', ∃ u ∈ B, c' u = i := by
    intro B hBS hBac hBc i hi
    have hinj : Set.InjOn c' (B : Set α) := by
      intro u hu v hv huv
      by_contra hne
      rcases hc'ch u (hBS hu) v (hBS hv) huv with h | h
      · exact hBac hu hv hne h
      · exact hBac hv hu (Ne.symm hne) h
    have himg : B.image c' = Finset.range w' := by
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        simp only [Finset.mem_image] at hj
        obtain ⟨u, hu, rfl⟩ := hj
        simpa using hc'lt u (hBS hu)
      · rw [Finset.card_image_of_injOn hinj]; simp [hBc]
    have : i ∈ B.image c' := by rw [himg]; simpa using hi
    simpa using this
  have htop : ∀ i < w', ∃ x ∈ S', c' x = i ∧
      (∃ B, B ⊆ S' ∧ IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = w' ∧ x ∈ B) ∧
      ∀ B, B ⊆ S' → IsAntichain (· ≤ ·) (B : Set α) → B.card = w' →
        ∀ u ∈ B, c' u = i → u ≤ x := by
    intro i hi
    set T := S'.filter (fun x => c' x = i ∧
      ∃ B, B ⊆ S' ∧ IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = w' ∧ x ∈ B) with hT
    have hTne : T.Nonempty := by
      obtain ⟨u, hu, hcu⟩ := hmeet A0 hA0S hA0ac hA0c i hi
      exact ⟨u, by simp only [hT, Finset.mem_filter]; exact ⟨hA0S hu, hcu, A0, hA0S, hA0ac, hA0c, hu⟩⟩
    obtain ⟨x, hx⟩ := T.exists_maximal hTne
    have hxT := hx.prop
    simp only [hT, Finset.mem_filter] at hxT
    refine ⟨x, hxT.1, hxT.2.1, hxT.2.2, ?_⟩
    intro B hBS hBac hBc u hu hcu
    have huT : u ∈ T := by
      simp only [hT, Finset.mem_filter]; exact ⟨hBS hu, hcu, B, hBS, hBac, hBc, hu⟩
    rcases hc'ch u (hBS hu) x hxT.1 (by rw [hcu, hxT.2.1]) with h | h
    · exact h
    · exact hx.2 huT h
  haveI : Nonempty α := ⟨m⟩
  choose! x hxS hxc hxB hxtop using htop
  by_cases hcase : ∃ i < w', x i < m
  · obtain ⟨i, hi, hxm⟩ := hcase
    set K := insert m (S'.filter (fun u => c' u = i ∧ u ≤ x i)) with hK
    set S'' := S.filter (fun u => u ∉ K) with hS''
    have hsub : S'' ⊂ S := by
      rw [hS'']
      exact Finset.filter_ssubset.2 ⟨m, hmS, by simp [hK]⟩
    have bound : ∀ A ⊆ S'', IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ w' - 1 := by
      intro A hA hAac
      by_contra hcon
      have hAS' : A ⊆ S' := by
        intro u hu
        have := hA hu
        simp only [hS'', Finset.mem_filter, hK, Finset.mem_insert, not_or] at this
        exact Finset.mem_erase.2 ⟨this.2.1, this.1⟩
      have hAc : A.card = w' := le_antisymm (hw'le A hAS' hAac) (by omega)
      obtain ⟨u, hu, hcu⟩ := hmeet A hAS' hAac hAc i hi
      have hux := hxtop i hi A hAS' hAac hAc u hu hcu
      have := hA hu
      simp only [hS'', Finset.mem_filter, hK, Finset.mem_insert, not_or] at this
      exact this.2.2 ⟨hAS' hu, hcu, hux⟩
    obtain ⟨c'', h1, h2⟩ := ih S'' hsub (w' - 1) bound
    refine ⟨fun y => if y ∈ K then w' - 1 else c'' y, ?_, ?_⟩
    · intro y hy
      by_cases hyK : y ∈ K
      · simp only [hyK, if_true]; omega
      · simp only [hyK, if_false]
        have := h1 y (Finset.mem_filter.2 ⟨hy, hyK⟩); omega
    · intro y hy z hz hyz
      by_cases hyK : y ∈ K <;> by_cases hzK : z ∈ K
      · -- both in K
        have hK' : ∀ u ∈ K, u = m ∨ (u ∈ S' ∧ c' u = i ∧ u ≤ x i) := by
          intro u hu
          simp only [hK, Finset.mem_insert, Finset.mem_filter] at hu
          tauto
        rcases hK' y hyK with rfl | ⟨hyS, hyc, hyx⟩ <;>
          rcases hK' z hzK with rfl | ⟨hzS, hzc, hzx⟩
        · exact Or.inl le_rfl
        · exact Or.inr (hzx.trans hxm.le)
        · exact Or.inl (hyx.trans hxm.le)
        · exact hc'ch y hyS z hzS (by rw [hyc, hzc])
      · simp only [hyK, hzK, if_true, if_false] at hyz
        have := h1 z (Finset.mem_filter.2 ⟨hz, hzK⟩); omega
      · simp only [hyK, hzK, if_true, if_false] at hyz
        have := h1 y (Finset.mem_filter.2 ⟨hy, hyK⟩); omega
      · simp only [hyK, hzK, if_false] at hyz
        exact h2 y (Finset.mem_filter.2 ⟨hy, hyK⟩) z (Finset.mem_filter.2 ⟨hz, hzK⟩) hyz
  · push_neg at hcase
    have hxne : ∀ i < w', x i ≠ m := fun i hi h => by
      have := hxS i hi; rw [h] at this; simp [hS'] at this
    have hxinj : Set.InjOn x (Finset.range w' : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      rw [← hxc i hi, ← hxc j hj, hij]
    set A := insert m ((Finset.range w').image x) with hA
    have hmA : m ∉ (Finset.range w').image x := by
      simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
      exact fun i hi h => hxne i hi h
    have hAcard : A.card = w' + 1 := by
      rw [hA, Finset.card_insert_of_notMem hmA, Finset.card_image_of_injOn hxinj]; simp
    have hAsub : A ⊆ S := by
      intro y hy
      simp only [hA, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hy
      rcases hy with rfl | ⟨i, hi, rfl⟩
      · exact hmS
      · exact hS'S (hxS i hi)
    have himgac : IsAntichain (· ≤ ·) (((Finset.range w').image x : Finset α) : Set α) := by
      intro a ha b hb hab hle
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ha hb
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      obtain ⟨B, hBS, hBac, hBc, hjB⟩ := hxB j hj
      obtain ⟨u, hu, hcu⟩ := hmeet B hBS hBac hBc i hi
      have hux := hxtop i hi B hBS hBac hBc u hu hcu
      have hij : i ≠ j := fun h => hab (by rw [h])
      have hune : u ≠ x j := fun h => hij (by rw [← hcu, h, hxc j hj])
      exact hBac hu hjB hune (hux.trans hle)
    have hAac : IsAntichain (· ≤ ·) (A : Set α) := by
      rw [hA, Finset.coe_insert]
      apply himgac.insert
      · intro b hb _ hle
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hb
        obtain ⟨i, hi, rfl⟩ := hb
        exact hcase i hi (lt_of_le_of_ne hle (hxne i hi))
      · intro b hb _ hle
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hb
        obtain ⟨i, hi, rfl⟩ := hb
        exact hxne i hi (hmax _ (hS'S (hxS i hi)) hle)
    have hwn : w' + 1 ≤ n := hAcard ▸ hn A hAsub hAac
    refine ⟨fun y => if y = m then w' else c' y, ?_, ?_⟩
    · intro y hy
      by_cases hym : y = m
      · simp only [hym, if_true]; omega
      · simp only [hym, if_false]
        have := hc'lt y (Finset.mem_erase.2 ⟨hym, hy⟩); omega
    · intro y hy z hz hyz
      by_cases hym : y = m <;> by_cases hzm : z = m
      · subst hym; subst hzm; exact Or.inl le_rfl
      · simp only [hym, hzm, if_true, if_false] at hyz
        have := hc'lt z (Finset.mem_erase.2 ⟨hzm, hz⟩); omega
      · simp only [hym, hzm, if_true, if_false] at hyz
        have := hc'lt y (Finset.mem_erase.2 ⟨hym, hy⟩); omega
      · simp only [hym, hzm, if_false] at hyz
        exact hc'ch y (Finset.mem_erase.2 ⟨hym, hy⟩) z (Finset.mem_erase.2 ⟨hzm, hz⟩) hyz

theorem dil_core (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ C : Fin (width α) → Finset α, IsChainPartition C) ∧
    ∀ (k : ℕ) (C : Fin k → Finset α), IsChainPartition C → width α ≤ k := by
  classical
  have hwle : ∀ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ width α := by
    intro A hA
    unfold width
    exact Finset.le_sup (f := Finset.card) (by simp [hA])
  constructor
  · obtain ⟨c, hc1, hc2⟩ := dil_claim (Finset.univ : Finset α) (width α)
      (fun A _ hA => hwle A hA)
    refine ⟨fun i => Finset.univ.filter (fun x => c x = i.val), ?_, ?_, ?_⟩
    · intro i a ha b hb _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      exact hc2 a (Finset.mem_univ _) b (Finset.mem_univ _) (ha.trans hb.symm)
    · intro i j hij
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hij (Fin.ext (ha.symm.trans hb))
    · intro x
      exact ⟨⟨c x, hc1 x (Finset.mem_univ _)⟩, by simp⟩
  · intro k C hC
    obtain ⟨hch, hdis, hcov⟩ := hC
    unfold width
    apply Finset.sup_le
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    choose f hf using hcov
    have hinj : Set.InjOn f (A : Set α) := by
      intro a ha b hb hab
      by_contra hne
      have hb' : b ∈ C (f a) := hab ▸ hf b
      rcases hch (f a) (hf a) hb' hne with h | h
      · exact hA ha hb hne h
      · exact hA hb ha (Ne.symm hne) h
    calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
      _ = k := by simp

end AppliedComb.Posets

open AppliedComb.Posets


theorem solution (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ C : Fin (width α) → Finset α, IsChainPartition C) ∧
    ∀ (k : ℕ) (C : Fin k → Finset α), IsChainPartition C → width α ≤ k := by
  exact dil_core α
