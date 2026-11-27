-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:53.439857+00:00
-- url     : https://prove2.me/submissions/65777640-6b6c-4321-9d76-fedc6235f707

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_Reports

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution {n : ℕ} :
    (∀ (D : ListDist n) (f : Finset (Fin n) → ℝ), IsIncreasingSetFn f →
        NonmonotoneSubmod.Shared.Submodular f → IsIC D (incrementMech f)) ∧
    (∀ x : List (Fin n) → Fin n → ℝ, IsICOn (allReports n) x →
      IsIncreasingSetFn (maxMass (allReports n) x) ∧
        NonmonotoneSubmod.Shared.Submodular (maxMass (allReports n) x)) := by
          classical
          refine ⟨?_, ?_⟩
          · intro D f hf hsub
            have hpre : ∀ (L M : List (Fin n)) (j : Fin n), j ∈ L →
                incrementMech f (L ++ M) j = incrementMech f L j := by
              intro L M j hj
              have hlt : L.idxOf j < L.length := List.idxOf_lt_length_of_mem hj
              have hidx : (L ++ M).idxOf j = L.idxOf j := List.idxOf_append_of_mem hj
              unfold incrementMech
              rw [if_pos (List.mem_append_left M hj), if_pos hj, hidx,
                List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
            have hnew : ∀ (L : List (Fin n)) (a : Fin n), a ∉ L →
                incrementMech f (L ++ [a]) a = f (insert a L.toFinset) - f L.toFinset := by
              intro L a ha
              have hidx : (L ++ [a]).idxOf a = L.length := by
                rw [List.idxOf_append_of_notMem ha]; simp
              unfold incrementMech
              rw [if_pos (by simp), hidx, List.take_of_length_le (by simp), List.take_left' rfl]
              congr 2
              ext y; simp
            have heq : ∀ L : List (Fin n), L.Nodup →
                ∑ j ∈ L.toFinset, incrementMech f L j = f L.toFinset - f ∅ := by
              intro L
              induction L using List.reverseRecOn with
              | nil => intro _; simp
              | append_singleton L a ih =>
                intro hnd
                have hnd' := List.nodup_append.mp hnd
                have ha : a ∉ L := fun h => hnd'.2.2 a h a (by simp) rfl
                have haF : a ∉ L.toFinset := by simpa using ha
                have hT : (L ++ [a]).toFinset = insert a L.toFinset := by
                  ext y; simp
                rw [hT, Finset.sum_insert haF, hnew L a ha]
                rw [Finset.sum_congr rfl (fun j hj => hpre L [a] j (List.mem_toFinset.mp hj)),
                  ih hnd'.1]
                ring
            have hineq : ∀ L : List (Fin n), L.Nodup → ∀ A : Finset (Fin n),
                ∑ j ∈ L.toFinset ∩ A, incrementMech f L j ≤ f (L.toFinset ∩ A) - f ∅ := by
              intro L
              induction L using List.reverseRecOn with
              | nil => intro _ A; simp
              | append_singleton L a ih =>
                intro hnd A
                have hnd' := List.nodup_append.mp hnd
                have ha : a ∉ L := fun h => hnd'.2.2 a h a (by simp) rfl
                have haF : a ∉ L.toFinset := by simpa using ha
                have hT : (L ++ [a]).toFinset = insert a L.toFinset := by
                  ext y; simp
                rw [hT]
                by_cases haA : a ∈ A
                · rw [Finset.insert_inter_of_mem haA,
                    Finset.sum_insert (fun h => haF (Finset.mem_inter.mp h).1), hnew L a ha]
                  rw [Finset.sum_congr rfl (fun j hj => hpre L [a] j
                    (List.mem_toFinset.mp (Finset.mem_inter.mp hj).1))]
                  have h1 := ih hnd'.1 A
                  have h2 := hsub L.toFinset (insert a (L.toFinset ∩ A))
                  have e1 : L.toFinset ∪ insert a (L.toFinset ∩ A) = insert a L.toFinset := by
                    ext y; simp; tauto
                  have e2 : L.toFinset ∩ insert a (L.toFinset ∩ A) = L.toFinset ∩ A := by
                    ext y; simp only [Finset.mem_inter, Finset.mem_insert, List.mem_toFinset]
                    constructor
                    · rintro ⟨h, h' | h'⟩
                      · subst h'; exact absurd h ha
                      · exact ⟨h, h'.2⟩
                    · rintro ⟨h, h'⟩; exact ⟨h, Or.inr ⟨h, h'⟩⟩
                  rw [e1, e2] at h2
                  linarith
                · rw [Finset.insert_inter_of_notMem haA]
                  rw [Finset.sum_congr rfl (fun j hj => hpre L [a] j
                    (List.mem_toFinset.mp (Finset.mem_inter.mp hj).1))]
                  exact ih hnd'.1 A
            refine ⟨?_, ?_, ?_⟩
            · intro ℓ hℓ k hk ℓ' hℓ'
              have hndk : (ℓ.take k).Nodup := (D.nodup ℓ hℓ).sublist (List.take_sublist k ℓ)
              rw [Finset.inter_comm]
              calc ∑ j ∈ ℓ'.toFinset ∩ (ℓ.take k).toFinset, incrementMech f ℓ' j
                  ≤ f (ℓ'.toFinset ∩ (ℓ.take k).toFinset) - f ∅ := hineq ℓ' (D.nodup ℓ' hℓ') _
                _ ≤ f (ℓ.take k).toFinset - f ∅ := by
                  linarith [hf.1 (Finset.inter_subset_right (s₁ := ℓ'.toFinset)
                    (s₂ := (ℓ.take k).toFinset))]
                _ = ∑ j ∈ (ℓ.take k).toFinset, incrementMech f (ℓ.take k) j := (heq _ hndk).symm
                _ = ∑ j ∈ (ℓ.take k).toFinset, incrementMech f ℓ j := by
                  refine Finset.sum_congr rfl (fun j hj => ?_)
                  have := hpre (ℓ.take k) (ℓ.drop k) j (List.mem_toFinset.mp hj)
                  rw [List.take_append_drop] at this
                  exact this.symm
            · intro ℓ hℓ
              rw [heq ℓ (D.nodup ℓ hℓ)]
              have h1 := (hf.2 ℓ.toFinset).2
              have h2 := (hf.2 ∅).1
              linarith
            · intro ℓ hℓ j hj
              unfold incrementMech
              rw [if_pos hj, sub_nonneg]
              apply hf.1
              intro y hy
              rw [List.mem_toFinset] at hy ⊢
              exact List.take_subset_take_left ℓ (Nat.le_succ _) hy
          · intro x hx
            obtain ⟨hIC, hsum, hnn⟩ := hx
            set R := allReports n with hR
            have hle : ∀ S, ∀ ℓ ∈ R, ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j ≤ maxMass R x S :=
              fun S ℓ hℓ => by
                unfold maxMass
                exact Finset.le_max' _ _
                  (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun ℓ => ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j) hℓ))
            have h0 : ∀ S, 0 ≤ maxMass R x S :=
              fun S => by unfold maxMass; exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
            have hub : ∀ S c, 0 ≤ c → (∀ ℓ ∈ R, ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j ≤ c) →
                maxMass R x S ≤ c := by
              intro S c hc h
              unfold maxMass
              apply Finset.max'_le
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_image] at hy
              rcases hy with rfl | ⟨ℓ, hℓ, rfl⟩
              · exact hc
              · exact h ℓ hℓ
            have hpref : ∀ (P Q : List (Fin n)) (A : Finset (Fin n)), P.toFinset = A → P ++ Q ∈ R →
                maxMass R x A ≤ ∑ j ∈ A, x (P ++ Q) j := by
              intro P Q A hA hPQ
              subst hA
              apply hub
              · apply Finset.sum_nonneg
                intro j hj
                exact hnn _ hPQ j (List.mem_append_left Q (List.mem_toFinset.mp hj))
              · intro ℓ' hℓ'
                have := hIC (P ++ Q) hPQ P.length (by simp) ℓ' hℓ'
                rwa [List.take_left' rfl] at this
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · intro S S' hSS'
              apply hub S _ (h0 S')
              intro ℓ hℓ
              refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.inter_subset_inter hSS' subset_rfl) ?_) (hle S' ℓ hℓ)
              intro j hj _
              exact hnn ℓ hℓ j (List.mem_toFinset.mp (Finset.mem_inter.mp hj).2)
            · intro S
              refine ⟨h0 S, hub S 1 zero_le_one ?_⟩
              intro ℓ hℓ
              refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
                Finset.inter_subset_right ?_) (hsum ℓ hℓ)
              intro j hj _
              exact hnn ℓ hℓ j (List.mem_toFinset.mp hj)
            · intro S T
              set L1 := (S ∩ T).toList
              set L2 := (S \ T).toList
              set L3 := (T \ S).toList
              have hmem : L1 ++ (L2 ++ L3) ∈ R := by
                rw [hR]
                simp only [allReports, Finset.mem_image, Finset.mem_univ, true_and]
                refine ⟨⟨L1 ++ (L2 ++ L3), ?_⟩, rfl⟩
                simp only [List.nodup_append, L1, L2, L3, Finset.nodup_toList, true_and,
                  Finset.mem_toList, Finset.mem_inter, Finset.mem_sdiff, List.mem_append]
                refine ⟨?_, ?_⟩
                · rintro a ha b hb rfl; tauto
                · rintro a ha b hb rfl; tauto
              have hmem2 : (L1 ++ L2) ++ L3 ∈ R := by rwa [List.append_assoc]
              have hmem3 : (L1 ++ (L2 ++ L3)) ++ [] ∈ R := by rwa [List.append_nil]
              have hA1 := hpref L1 (L2 ++ L3) (S ∩ T) (by simp [L1]) hmem
              have hA2 := hpref (L1 ++ L2) L3 S (by
                ext y; simp only [L1, L2, L3, List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
                  Finset.mem_inter, Finset.mem_sdiff]
                by_cases hS : y ∈ S <;> by_cases hT : y ∈ T <;> simp [hS, hT]) hmem2
              have hA3 := hpref (L1 ++ (L2 ++ L3)) [] (S ∪ T) (by
                ext y; simp only [L1, L2, L3, List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
                  Finset.mem_inter, Finset.mem_sdiff]
                by_cases hS : y ∈ S <;> by_cases hT : y ∈ T <;> simp [hS, hT]) hmem3
              rw [List.append_assoc] at hA2
              rw [List.append_nil] at hA3
              have hA4 := hle T _ hmem
              have hTi : T ∩ (L1 ++ (L2 ++ L3)).toFinset = T := by
                ext y; simp only [L1, L2, L3, List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
                  Finset.mem_inter, Finset.mem_sdiff]
                by_cases hS : y ∈ S <;> by_cases hT : y ∈ T <;> simp [hS, hT]
              rw [hTi] at hA4
              have hA5 := hle S _ hmem
              have hSi : S ∩ (L1 ++ (L2 ++ L3)).toFinset = S := by
                ext y; simp only [L1, L2, L3, List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
                  Finset.mem_inter, Finset.mem_sdiff]
                by_cases hS : y ∈ S <;> by_cases hT : y ∈ T <;> simp [hS, hT]
              rw [hSi] at hA5
              have := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := x (L1 ++ (L2 ++ L3)))
              linarith
