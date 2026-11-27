-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:01.985452+00:00
-- url     : https://prove2.me/submissions/24f6aa87-5023-45b7-af9a-e6fc1b3fa62f

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution {n : ℕ} (D : ListDist n) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (B : ℝ) (hB : B ∈ Set.Icc (0 : ℝ) 1) :
    (1 / Real.exp 1) * revMech D r (budgetMech w B) ≤
      revIndependent D r (expInclusion w) := by
        classical
        have hana : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
            (1 / Real.exp 1) * (min (a + b) B - min a B) ≤
              Real.exp (-a) * (1 - Real.exp (-b)) := by
          intro a b ha hb
          by_cases hab : B ≤ a
          · rw [min_eq_right hab, min_eq_right (by linarith : B ≤ a + b), sub_self, mul_zero]
            exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hb)))
          · have haB : a ≤ B := le_of_lt (lt_of_not_ge hab)
            let c := min b (B-a)
            have hc : 0 ≤ c := le_min hb (sub_nonneg.mpr haB)
            have hcb : c ≤ b := min_le_left _ _
            have hca : a + c ≤ 1 := by have := min_le_right b (B-a); dsimp [c] at *; linarith [hB.2]
            have hd : min (a+b) B - min a B = c := by
              rw [min_eq_left haB]
              dsimp [c]
              rcases le_total (a+b) B with h | h
              · rw [min_eq_left h, min_eq_left (by linarith)]; ring
              · rw [min_eq_right h, min_eq_right (by linarith)]
            have he : c * Real.exp (-c) ≤ 1 - Real.exp (-c) := by
              have ht := mul_le_mul_of_nonneg_right (Real.add_one_le_exp c) (Real.exp_pos (-c)).le
              have hx : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
              nlinarith
            have he' : Real.exp (-a) * (c * Real.exp (-c)) ≤ Real.exp (-a) * (1 - Real.exp (-b)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              exact he.trans (by have := Real.exp_le_exp.mpr (neg_le_neg hcb); linarith)
            rw [hd]
            calc
              (1 / Real.exp 1) * c = Real.exp (-1) * c := by rw [Real.exp_neg]; simp
              _ ≤ Real.exp (-(a+c)) * c := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hc
              _ = Real.exp (-a) * (c * Real.exp (-c)) := by rw [neg_add, Real.exp_add]; ring
              _ ≤ _ := he'
        have hchoice : ∀ (l : List (Fin n)) (j : Fin n), l.Nodup → j ∈ l →
            ∀ T : Finset (Fin n), Chooses T l j ↔
              j ∈ T ∧ Disjoint (l.take (l.idxOf j)).toFinset T := by
          intro l
          induction l with
          | nil => simp
          | cons a l ih =>
            intro j hl hj T
            have hnd := List.nodup_cons.mp hl
            by_cases haj : a = j
            · subst a
              have hn : l.find? (fun i => decide (i ∈ T)) ≠ some j := by
                intro h
                exact hnd.1 (List.mem_of_find?_eq_some h)
              by_cases hjT : j ∈ T <;> simp [Chooses, List.find?_cons, hjT, hn]
            · have hja : j ≠ a := Ne.symm haj
              have hjl : j ∈ l := by simpa [hja] using hj
              rw [List.idxOf_cons_ne l haj, List.take_succ_cons, List.toFinset_cons]
              by_cases haT : a ∈ T
              · simp [Chooses, List.find?_cons, haT, haj, Finset.disjoint_insert_left]
              · simpa [Chooses, List.find?_cons, haT, Finset.disjoint_insert_left] using ih j hnd.2 hjl T
        have hforce : ∀ (q : Fin n → ℝ) (P : Finset (Fin n)) (j : Fin n), j ∉ P →
            (∑ T ∈ Finset.univ.powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                (if j ∈ T ∧ Disjoint P T then (1:ℝ) else 0)) =
              q j * ∏ k ∈ P, (1-q k) := by
          intro q P j hjP
          let f := fun k => q k * (if k ∈ P then (0:ℝ) else 1)
          let g := fun k => (1-q k) * (if j = k then (0:ℝ) else 1)
          have hterm : ∀ T : Finset (Fin n),
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                (if j ∈ T ∧ Disjoint P T then (1:ℝ) else 0) =
              (∏ k ∈ T, f k) * ∏ k ∈ Finset.univ \ T, g k := by
            intro T
            rw [show (∏ k ∈ T, f k) = (∏ k ∈ T, q k) * ∏ k ∈ T, (if k ∈ P then (0:ℝ) else 1) by
              dsimp [f]; rw [Finset.prod_mul_distrib]]
            rw [show (∏ k ∈ Finset.univ \ T, g k) = (∏ k ∈ Finset.univ \ T, (1-q k)) *
                ∏ k ∈ Finset.univ \ T, (if j = k then (0:ℝ) else 1) by
              dsimp [g]; rw [Finset.prod_mul_distrib]]
            by_cases hdis : Disjoint P T
            · have hp : (∏ k ∈ T, (if k ∈ P then (0:ℝ) else 1)) = 1 := by
                apply Finset.prod_eq_one
                intro k hk
                simp [show k ∉ P from fun h => Finset.disjoint_left.mp hdis h hk]
              rw [hp]
              by_cases hjT : j ∈ T
              · have hg : (∏ k ∈ Finset.univ \ T, (if j = k then (0:ℝ) else 1)) = 1 := by
                  apply Finset.prod_eq_one
                  intro k hk
                  have hkj : j ≠ k := by intro h; subst k; exact (Finset.mem_sdiff.mp hk).2 hjT
                  simp [hkj]
                simp [hg, hjT, hdis, SpectralSparsify.Sampling.outcomeProb]
              · have hg : (∏ k ∈ Finset.univ \ T, (if j = k then (0:ℝ) else 1)) = 0 := by
                  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjT⟩)
                  simp
                simp [hg, hjT]
            · have hp : (∏ k ∈ T, (if k ∈ P then (0:ℝ) else 1)) = 0 := by
                obtain ⟨k, hkP, hkT⟩ := Finset.not_disjoint_iff.mp hdis
                apply Finset.prod_eq_zero hkT
                simp [hkP]
              simp [hp, hdis]
          simp_rw [hterm]
          rw [← Finset.prod_add]
          have hf : ∀ k, f k + g k =
              (if k ∈ P then (1-q k) else 1) * (if j = k then q k else 1) := by
            intro k
            by_cases hkP : k ∈ P <;> by_cases hjk : j = k <;> simp_all [f, g]
          simp_rw [hf]
          rw [Finset.prod_mul_distrib]
          rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
          rw [Finset.prod_ite_eq]
          simp [mul_comm]
        have hnotpref : ∀ (l : List (Fin n)) (j : Fin n), j ∈ l →
            j ∉ (l.take (l.idxOf j)).toFinset := by
          intro l j hj
          simpa only [List.mem_toFinset, List.mem_take_iff_idxOf_lt hj, lt_self_iff_false, not_false_eq_true]
        have halloc : ∀ (l : List (Fin n)) (j : Fin n), j ∈ l →
            budgetMech w B l j =
              min ((∑ k ∈ (l.take (l.idxOf j)).toFinset, w k) + w j) B -
                min (∑ k ∈ (l.take (l.idxOf j)).toFinset, w k) B := by
          intro l j hj
          unfold budgetMech incrementMech budgetFn
          rw [if_pos hj, List.take_add_one, List.getElem?_idxOf hj]
          simp only [Option.toList_some, List.toFinset_append, List.toFinset_cons,
            List.toFinset_nil, Finset.union_insert, Finset.union_empty, Finset.sum_insert (hnotpref l j hj)]
          rw [add_comm (w j)]
        have hmarg : ∀ (l : List (Fin n)) (j : Fin n), l.Nodup → j ∈ l →
            (∑ T ∈ Finset.univ.powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ (expInclusion w) T *
                (if Chooses T l j then (1:ℝ) else 0)) =
              Real.exp (-(∑ k ∈ (l.take (l.idxOf j)).toFinset, w k)) *
                (1-Real.exp (-w j)) := by
          intro l j hl hj
          simp_rw [hchoice l j hl hj]
          rw [hforce (expInclusion w) _ j (hnotpref l j hj)]
          simp only [expInclusion, sub_sub_cancel]
          rw [← Real.exp_sum, Finset.sum_neg_distrib, mul_comm]
        have hcmem : ∀ (S : Finset (Fin n)) (l : List (Fin n)) (j : Fin n),
            Chooses S l j → j ∈ S ∧ j ∈ l := by
          intro S l j h
          have hh := List.find?_eq_some_iff_append.mp h
          exact ⟨by simpa using hh.1, List.mem_of_find?_eq_some h⟩
        have hrev : ∀ S : Finset (Fin n), revAssort D r S =
            ∑ l ∈ D.supp, D.p l * ∑ j ∈ l.toFinset, r j *
              (if Chooses S l j then (1:ℝ) else 0) := by
          intro S
          unfold revAssort choiceProb
          simp_rw [Finset.sum_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          have hc : ∀ j : Fin n, r j * (if Chooses S l j then D.p l else 0) =
              D.p l * (r j * (if Chooses S l j then (1:ℝ) else 0)) := by
            intro j
            split_ifs <;> ring
          simp_rw [hc]
          have hs : (∑ j ∈ S, D.p l * (r j * (if Chooses S l j then (1:ℝ) else 0))) =
              ∑ j : Fin n, D.p l * (r j * (if Chooses S l j then (1:ℝ) else 0)) := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro j _ hj
            have hn : ¬ Chooses S l j := fun h => hj (hcmem S l j h).1
            simp [hn]
          rw [hs]
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hn : ¬ Chooses S l j := fun h => hj (List.mem_toFinset.mpr (hcmem S l j h).2)
          simp [hn]
        have htotal : revIndependent D r (expInclusion w) =
            ∑ l ∈ D.supp, D.p l * ∑ j ∈ l.toFinset,
              r j * (Real.exp (-(∑ k ∈ (l.take (l.idxOf j)).toFinset, w k)) *
                (1-Real.exp (-w j))) := by
          unfold revIndependent SpectralSparsify.Sampling.expect
          simp_rw [hrev, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← hmarg l j (D.nodup l hl) (List.mem_toFinset.mp hj)]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hT
          ring
        rw [htotal]
        unfold revMech
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        rw [← mul_assoc, mul_comm (1 / Real.exp 1) (D.p l), mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (D.pos l hl).le
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_assoc, mul_comm (1 / Real.exp 1) (r j), mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (hr j)
        rw [halloc l j (List.mem_toFinset.mp hj)]
        exact hana _ _ (Finset.sum_nonneg (fun k _ => hw k)) (hw j)
