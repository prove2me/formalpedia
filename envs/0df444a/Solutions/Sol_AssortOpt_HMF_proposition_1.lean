-- Prove2me | solution 1 for AssortOpt.HMF.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:12:53.324783+00:00
-- url     : https://prove2.me/submissions/487698fe-1cd6-4ae4-9ef6-83870c295c19

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

namespace HMFProp1Aux

variable {n : ℕ}

lemma chooses_iff (S : Finset (Fin n)) (ℓ : List (Fin n)) (j : Fin n) :
    Chooses S ℓ j ↔ j ∈ S ∧ ∃ (i : ℕ) (h : i < ℓ.length), ℓ[i] = j ∧
      ∀ i' (h' : i' < i), ℓ[i']'(by omega) ∉ S := by
  unfold Chooses
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hj, i, h, he, hlt⟩
    refine ⟨by simpa using hj, i, h, he, fun i' h' => ?_⟩
    simpa using hlt i' h'
  · rintro ⟨hj, i, h, he, hlt⟩
    refine ⟨by simpa using hj, i, h, he, fun i' h' => ?_⟩
    simpa using hlt i' h'

lemma chooses_mem {S : Finset (Fin n)} {ℓ : List (Fin n)} {j : Fin n} (h : Chooses S ℓ j) :
    j ∈ S ∧ j ∈ ℓ := by
  refine ⟨?_, List.mem_of_find?_eq_some h⟩
  have := List.find?_some h
  simpa using this

lemma chooses_unique {S : Finset (Fin n)} {ℓ : List (Fin n)} {j j' : Fin n}
    (h : Chooses S ℓ j) (h' : Chooses S ℓ j') : j = j' := by
  unfold Chooses at h h'
  rw [h] at h'
  exact Option.some.inj h'

lemma chooses_take {S : Finset (Fin n)} {ℓ : List (Fin n)} (k : ℕ)
    (h : ∃ i ∈ ℓ.take k, i ∈ S) : ∃ j0 ∈ ℓ.take k, Chooses S ℓ j0 := by
  have hs : ((ℓ.take k).find? (fun i => decide (i ∈ S))).isSome := by
    rw [List.find?_isSome]
    obtain ⟨i, hi, hiS⟩ := h
    exact ⟨i, hi, by simpa using hiS⟩
  obtain ⟨j0, hj0⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨j0, List.mem_of_find?_eq_some hj0, ?_⟩
  unfold Chooses
  rw [← List.take_append_drop k ℓ, List.find?_append, hj0]
  rfl

lemma sum_ind_le_one (S : Finset (Fin n)) (ℓ : List (Fin n)) (A : Finset (Fin n)) :
    ∑ j ∈ A, assortMech S ℓ j ≤ 1 := by
  classical
  unfold assortMech
  rw [Finset.sum_boole]
  have : (A.filter (fun j => Chooses S ℓ j)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact chooses_unique ha.2 hb.2
  exact_mod_cast this

lemma assortMech_nonneg (S : Finset (Fin n)) (ℓ : List (Fin n)) (j : Fin n) :
    0 ≤ assortMech S ℓ j := by
  unfold assortMech; split_ifs <;> norm_num

lemma isIC_assort (D : ListDist n) (S : Finset (Fin n)) : IsIC D (assortMech S) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ _ k _ ℓ' _
    by_cases hex : ∃ i ∈ ℓ.take k, i ∈ S
    · obtain ⟨j0, hj0, hch⟩ := chooses_take k hex
      have h1 : ∑ j ∈ (ℓ.take k).toFinset ∩ ℓ'.toFinset, assortMech S ℓ' j ≤ 1 :=
        sum_ind_le_one S ℓ' _
      have h2 : assortMech S ℓ j0 ≤ ∑ j ∈ (ℓ.take k).toFinset, assortMech S ℓ j :=
        Finset.single_le_sum (fun j _ => assortMech_nonneg S ℓ j)
          (List.mem_toFinset.mpr hj0)
      have h3 : assortMech S ℓ j0 = 1 := by unfold assortMech; simp [hch]
      linarith
    · push Not at hex
      have h0 : ∑ j ∈ (ℓ.take k).toFinset ∩ ℓ'.toFinset, assortMech S ℓ' j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_inter, List.mem_toFinset] at hj
        unfold assortMech
        rw [if_neg]
        intro hc
        exact hex j hj.1 (chooses_mem hc).1
      rw [h0]
      exact Finset.sum_nonneg (fun j _ => assortMech_nonneg S ℓ j)
  · intro ℓ _
    exact sum_ind_le_one S ℓ _
  · intro ℓ _ j _
    exact assortMech_nonneg S ℓ j

lemma rev_assort (D : ListDist n) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    revMech D r (assortMech S) = revAssort D r S := by
  classical
  unfold revMech revAssort choiceProb
  have hinner : ∀ ℓ : List (Fin n), ∑ j ∈ ℓ.toFinset, r j * assortMech S ℓ j =
      ∑ j ∈ S, r j * assortMech S ℓ j := by
    intro ℓ
    have e1 : ∑ j ∈ ℓ.toFinset, r j * assortMech S ℓ j =
        ∑ j ∈ Finset.univ, r j * assortMech S ℓ j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      unfold assortMech
      rw [if_neg, mul_zero]
      intro hc
      exact hj (List.mem_toFinset.mpr (chooses_mem hc).2)
    have e2 : ∑ j ∈ S, r j * assortMech S ℓ j =
        ∑ j ∈ Finset.univ, r j * assortMech S ℓ j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      unfold assortMech
      rw [if_neg, mul_zero]
      intro hc
      exact hj (chooses_mem hc).1
    rw [e1, e2]
  simp_rw [hinner, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ℓ _
  unfold assortMech
  split_ifs <;> ring

lemma det_IC_assort (D : ListDist n) (x : List (Fin n) → Fin n → ℝ) (hx : IsIC D x)
    (hdet : ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = 0 ∨ x ℓ j = 1) :
    ∃ S : Finset (Fin n), ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = assortMech S ℓ j := by
  classical
  obtain ⟨h3, h4, h5⟩ := hx
  let S : Finset (Fin n) := Finset.univ.filter (fun j => ∃ ℓ' ∈ D.supp, j ∈ ℓ' ∧ x ℓ' j = 1)
  have hS : ∀ j, j ∈ S ↔ ∃ ℓ' ∈ D.supp, j ∈ ℓ' ∧ x ℓ' j = 1 := by
    intro j; simp [S]
  -- LHS of IC is at least one when the prefix contains an item of S
  have lhs_ge : ∀ ℓ ∈ D.supp, ∀ k ≤ ℓ.length, ∀ i ∈ ℓ.take k, i ∈ S →
      1 ≤ ∑ j ∈ (ℓ.take k).toFinset, x ℓ j := by
    intro ℓ hℓ k hk i hi hiS
    obtain ⟨ℓ', hℓ', hiℓ', hx1⟩ := (hS i).mp hiS
    have := h3 ℓ hℓ k hk ℓ' hℓ'
    have hle : x ℓ' i ≤ ∑ j ∈ (ℓ.take k).toFinset ∩ ℓ'.toFinset, x ℓ' j :=
      Finset.single_le_sum (fun j hj => h5 ℓ' hℓ' j (List.mem_toFinset.mp
        (Finset.mem_inter.mp hj).2))
        (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hi, List.mem_toFinset.mpr hiℓ'⟩)
    linarith
  refine ⟨S, fun ℓ hℓ j hj => ?_⟩
  have hnd := D.nodup ℓ hℓ
  -- forward: x ℓ j = 1 → Chooses S ℓ j
  have fwd : x ℓ j = 1 → Chooses S ℓ j := by
    intro hxj
    have hjS : j ∈ S := (hS j).mpr ⟨ℓ, hℓ, hj, hxj⟩
    obtain ⟨j0, hj0⟩ : ∃ j0, Chooses S ℓ j0 := by
      obtain ⟨m, hm, hmj⟩ := List.getElem_of_mem hj
      obtain ⟨j0, -, hc⟩ := chooses_take (S := S) (ℓ := ℓ) ℓ.length
        ⟨j, by rw [List.take_length]; exact hj, hjS⟩
      exact ⟨j0, hc⟩
    by_cases hjj : j0 = j
    · rw [← hjj]; exact hj0
    exfalso
    obtain ⟨hj0S, i0, hi0, he0, hbefore⟩ := (chooses_iff S ℓ j0).mp hj0
    obtain ⟨m, hm, hmj⟩ := List.getElem_of_mem hj
    have hmi : i0 < m := by
      rcases lt_trichotomy i0 m with h | h | h
      · exact h
      · subst h; exact absurd (he0.symm.trans hmj) hjj
      · exact absurd (hmj ▸ hjS) (hbefore m h)
    have hk : i0 + 1 ≤ ℓ.length := hi0
    have hin : j0 ∈ ℓ.take (i0 + 1) := by
      rw [List.mem_take_iff_getElem]
      exact ⟨i0, by simp; omega, by simp [he0]⟩
    have hge := lhs_ge ℓ hℓ (i0 + 1) hk j0 hin hj0S
    have hjnot : j ∉ (ℓ.take (i0 + 1)).toFinset := by
      rw [List.mem_toFinset, List.mem_take_iff_getElem]
      rintro ⟨m', hm', hm'j⟩
      have hm'l : m' < ℓ.length := by simp at hm'; omega
      have : m' = m := by
        have h1 : ℓ[m'] = ℓ[m] := by rw [← hmj] at hm'j; simpa using hm'j
        exact (List.Nodup.getElem_inj_iff hnd).mp h1
      simp at hm'; omega
    have hsub : (ℓ.take (i0 + 1)).toFinset ⊆ ℓ.toFinset.erase j := by
      intro a ha
      rw [Finset.mem_erase]
      refine ⟨fun h => hjnot (h ▸ ha), ?_⟩
      rw [List.mem_toFinset] at ha ⊢
      exact List.mem_of_mem_take ha
    have hle1 : ∑ a ∈ (ℓ.take (i0 + 1)).toFinset, x ℓ a ≤ ∑ a ∈ ℓ.toFinset.erase j, x ℓ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ =>
        h5 ℓ hℓ a (List.mem_toFinset.mp (Finset.mem_of_mem_erase ha)))
    have hsplit := Finset.sum_erase_add ℓ.toFinset (fun a => x ℓ a) (List.mem_toFinset.mpr hj)
    have := h4 ℓ hℓ
    linarith
  -- backward: Chooses S ℓ j → x ℓ j = 1
  have bwd : Chooses S ℓ j → x ℓ j = 1 := by
    intro hc
    obtain ⟨hjS, m, hm, hmj, hbefore⟩ := (chooses_iff S ℓ j).mp hc
    have hin : j ∈ ℓ.take (m + 1) := by
      rw [List.mem_take_iff_getElem]
      exact ⟨m, by simp; omega, by simp [hmj]⟩
    have hge := lhs_ge ℓ hℓ (m + 1) hm j hin hjS
    have hsum : ∑ a ∈ (ℓ.take (m + 1)).toFinset, x ℓ a = x ℓ j := by
      apply Finset.sum_eq_single_of_mem j (List.mem_toFinset.mpr hin)
      intro a ha hne
      rw [List.mem_toFinset, List.mem_take_iff_getElem] at ha
      obtain ⟨i', hi', hia⟩ := ha
      have hi'l : i' < ℓ.length := by simp at hi'; omega
      have hi'm : i' ≠ m := by
        rintro rfl
        exact hne (by rw [← hmj, ← hia])
      have hi'lt : i' < m := by simp at hi'; omega
      have hnot : a ∉ S := by
        have := hbefore i' hi'lt
        rw [← hia]; simpa using this
      have ha_mem : a ∈ ℓ := by rw [← hia]; simp
      rcases hdet ℓ hℓ a ha_mem with h0 | h1
      · exact h0
      · exact absurd ((hS a).mpr ⟨ℓ, hℓ, ha_mem, h1⟩) hnot
    rw [hsum] at hge
    rcases hdet ℓ hℓ j hj with h0 | h1
    · linarith
    · exact h1
  unfold assortMech
  split_ifs with hc
  · exact bwd hc
  · rcases hdet ℓ hℓ j hj with h0 | h1
    · exact h0
    · exact absurd (fwd h1) hc

end HMFProp1Aux

open HMFProp1Aux in
theorem solution {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (∀ S : Finset (Fin n), IsIC D (assortMech S) ∧ revMech D r (assortMech S) = revAssort D r S) ∧
    (∀ S : Finset (Fin n), ∃ x, IsIC D x ∧ revAssort D r S ≤ revMech D r x) ∧
    (∀ x : List (Fin n) → Fin n → ℝ, IsIC D x →
      (∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = 0 ∨ x ℓ j = 1) →
      ∃ S : Finset (Fin n), ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = assortMech S ℓ j) := by
  refine ⟨fun S => ⟨isIC_assort D S, rev_assort D r S⟩, fun S => ⟨assortMech S, isIC_assort D S,
    (rev_assort D r S).ge⟩, fun x hx hdet => det_IC_assort D x hx hdet⟩
