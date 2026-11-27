-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:04.594525+00:00
-- url     : https://prove2.me/submissions/83ef64a2-7455-40d3-b3b4-6b7c972b6da3

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution {n : ℕ} (D : ListDist n) (R : Finset (List (Fin n)))
    (hR : ∀ ℓ ∈ R, ℓ.Nodup) (hsupp : D.supp ⊆ R)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (x : List (Fin n) → Fin n → ℝ) (hx : IsICOn R x) :
    (maxLength D = 0 →
      revMech D r x = 0 ∧
        revIndependent D r (fun j => cappedInclusion (maxLength D) (maxAlloc R x j)) = 0) ∧
    lengthFactor (maxLength D) * revMech D r x ≤
      revIndependent D r (fun j => cappedInclusion (maxLength D) (maxAlloc R x j)) := by
        classical
        set L := maxLength D with hL
        have ha0 : ∀ j, 0 ≤ maxAlloc R x j := fun j => by
          unfold maxAlloc; exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
        have hlenL : ∀ ℓ ∈ D.supp, ℓ.length ≤ L := fun ℓ hℓ => Finset.le_sup (f := List.length) hℓ
        have hzero : L = 0 → revMech D r x = 0 ∧
            revIndependent D r (fun j => cappedInclusion L (maxAlloc R x j)) = 0 := by
          intro h0
          constructor
          · unfold revMech
            apply Finset.sum_eq_zero
            intro ℓ hℓ
            have : ℓ = [] := List.eq_nil_of_length_eq_zero (by have := hlenL ℓ hℓ; omega)
            simp [this]
          · unfold revIndependent SpectralSparsify.Sampling.expect
            apply Finset.sum_eq_zero
            intro T _
            by_cases hT : T = ∅
            · subst hT; simp [revAssort]
            · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
              have : ∏ e ∈ T, cappedInclusion L (maxAlloc R x e) = 0 :=
                Finset.prod_eq_zero hj (by simp [cappedInclusion, h0])
              simp [SpectralSparsify.Sampling.outcomeProb, this]
        refine ⟨hzero, ?_⟩
        rcases Nat.eq_zero_or_pos L with h0 | hLpos
        · rw [(hzero h0).2, lengthFactor, if_pos h0, zero_mul]
        have hLne : L ≠ 0 := Nat.pos_iff_ne_zero.mp hLpos
        set q : Fin n → ℝ := fun j => cappedInclusion L (maxAlloc R x j) with hq
        have hLR : (0:ℝ) < L := by exact_mod_cast hLpos
        have hL1 : (1:ℝ) ≤ L := by exact_mod_cast hLpos
        have hqnn : ∀ j, 0 ≤ q j := by
          intro j; simp only [hq, cappedInclusion, if_neg hLne]
          split_ifs
          · exact div_nonneg (by linarith [ha0 j]) hLR.le
          · exact div_nonneg zero_le_one hLR.le
        have hqle : ∀ j, q j ≤ 1 / L := by
          intro j; simp only [hq, cappedInclusion, if_neg hLne]
          split_ifs with h
          · exact div_le_div_of_nonneg_right (by linarith) hLR.le
          · exact le_refl _
        have hq1 : ∀ j, q j ≤ 1 := fun j => (hqle j).trans (by rw [div_le_one hLR]; exact hL1)
        have hoP : ∀ T, 0 ≤ SpectralSparsify.Sampling.outcomeProb Finset.univ q T := fun T =>
          mul_nonneg (Finset.prod_nonneg fun e _ => hqnn e)
            (Finset.prod_nonneg fun e _ => by linarith [hq1 e])
        let A : List (Fin n) → Fin n → Finset (Fin n) := fun ℓ j => (ℓ.take (ℓ.idxOf j)).toFinset
        have hchoose : ∀ ℓ j (T : Finset (Fin n)), j ∈ ℓ → j ∈ T → Disjoint (A ℓ j) T →
            Chooses T ℓ j := by
          intro ℓ j T hj hjT hdis
          have hk : ℓ.idxOf j < ℓ.length := List.idxOf_lt_length_of_mem hj
          unfold Chooses
          rw [← List.take_append_drop (ℓ.idxOf j) ℓ, List.drop_eq_getElem_cons hk,
            List.getElem_idxOf hk, List.find?_append]
          have : (ℓ.take (ℓ.idxOf j)).find? (fun i => decide (i ∈ T)) = none := by
            rw [List.find?_eq_none]
            intro y hy
            have : y ∈ A ℓ j := List.mem_toFinset.mpr hy
            simpa using Finset.disjoint_left.mp hdis this
          rw [this]; simp [hjT]
        have hnotA : ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, j ∉ A ℓ j := by
          intro ℓ hℓ j hj hjA
          have hk := List.idxOf_lt_length_of_mem hj
          have hnd := D.nodup ℓ hℓ
          rw [← List.take_append_drop (ℓ.idxOf j) ℓ, List.drop_eq_getElem_cons hk,
            List.getElem_idxOf hk, List.nodup_append] at hnd
          exact hnd.2.2 j (List.mem_toFinset.mp hjA) j (by simp) rfl
        have hprob : ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ,
            ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                (if j ∈ T ∧ Disjoint (A ℓ j) T then (1:ℝ) else 0) =
              q j * ∏ i ∈ A ℓ j, (1 - q i) := by
          intro ℓ hℓ j hj
          have hjA := hnotA ℓ hℓ j hj
          set B := A ℓ j with hB
          have key := Finset.prod_add (fun e => if e ∈ B then (0:ℝ) else q e)
            (fun e => if e = j then (0:ℝ) else 1 - q e) Finset.univ
          have lhs : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                (if j ∈ T ∧ Disjoint B T then (1:ℝ) else 0) =
              ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
                (∏ i ∈ t, (fun e => if e ∈ B then (0:ℝ) else q e) i) *
                  ∏ i ∈ Finset.univ \ t, (fun e => if e = j then (0:ℝ) else 1 - q e) i := by
            apply Finset.sum_congr rfl; intro t _
            unfold SpectralSparsify.Sampling.outcomeProb
            by_cases h : j ∈ t ∧ Disjoint B t
            · rw [if_pos h, mul_one]
              congr 1
              · apply Finset.prod_congr rfl; intro e he
                dsimp only; rw [if_neg]; exact fun heB => Finset.disjoint_left.mp h.2 heB he
              · apply Finset.prod_congr rfl; intro e he
                dsimp only; rw [if_neg]; rintro rfl; exact (Finset.mem_sdiff.mp he).2 h.1
            · rw [if_neg h, mul_zero]
              rcases not_and_or.mp h with h1 | h2
              · symm; apply mul_eq_zero_of_right
                exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩) (if_pos rfl)
              · symm; apply mul_eq_zero_of_left
                obtain ⟨e, heB, het⟩ := Finset.not_disjoint_iff.mp h2
                exact Finset.prod_eq_zero het (if_pos heB)
          rw [lhs, ← key, ← Finset.prod_sdiff (Finset.subset_univ B)]
          congr 1
          · rw [Finset.prod_eq_single_of_mem j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjA⟩)]
            · simp [hjA]
            · intro b hb hbj
              rw [if_neg (Finset.mem_sdiff.mp hb).2, if_neg hbj]; ring
          · apply Finset.prod_congr rfl; intro e he
            rw [if_pos he, if_neg (fun h => hjA (by rw [← h]; exact he)), zero_add]
        have hterm : ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ,
            lengthFactor L * x ℓ j ≤ q j * ∏ i ∈ A ℓ j, (1 - q i) := by
          intro ℓ hℓ j hj
          have hℓR := hsupp hℓ
          have hxnn : ∀ i ∈ ℓ, 0 ≤ x ℓ i := hx.2.2 ℓ hℓR
          set P := ∑ i ∈ A ℓ j, x ℓ i with hPdef
          have hAsub : A ℓ j ⊆ ℓ.toFinset := fun i hi =>
            List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hi))
          have hP0 : 0 ≤ P := Finset.sum_nonneg fun i hi => hxnn i (List.mem_toFinset.mp (hAsub hi))
          have hx0 : 0 ≤ x ℓ j := hxnn j hj
          have hxP : x ℓ j + P ≤ 1 := by
            have : x ℓ j + P = ∑ i ∈ insert j (A ℓ j), x ℓ i :=
              (Finset.sum_insert (hnotA ℓ hℓ j hj)).symm
            rw [this]
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hx.2.1 ℓ hℓR)
            · exact Finset.insert_subset (List.mem_toFinset.mpr hj) hAsub
            · intro i hi _; exact hxnn i (List.mem_toFinset.mp hi)
          have haj : x ℓ j ≤ maxAlloc R x j := by
            unfold maxAlloc
            apply Finset.le_max'
            apply Finset.mem_insert_of_mem
            exact Finset.mem_image.mpr ⟨ℓ, Finset.mem_filter.mpr ⟨hℓR, hj⟩, rfl⟩
          have hai : ∀ i ∈ A ℓ j, maxAlloc R x i ≤ P := by
            intro i hi
            unfold maxAlloc
            apply Finset.max'_le
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact hP0
            · obtain ⟨ℓ', hℓ', rfl⟩ := Finset.mem_image.mp hy
              obtain ⟨hℓ'R, hiℓ'⟩ := Finset.mem_filter.mp hℓ'
              have hIC := hx.1 ℓ hℓR (ℓ.idxOf j) (List.idxOf_lt_length_of_mem hj).le ℓ' hℓ'R
              refine le_trans ?_ hIC
              exact Finset.single_le_sum (f := fun m => x ℓ' m)
                (fun m hm => hx.2.2 ℓ' hℓ'R m (List.mem_toFinset.mp (Finset.mem_inter.mp hm).2))
                (Finset.mem_inter.mpr ⟨hi, List.mem_toFinset.mpr hiℓ'⟩)
          have hqj : min (2 * x ℓ j) 1 / L ≤ q j := by
            simp only [hq, cappedInclusion, if_neg hLne]
            split_ifs with h
            · apply div_le_div_of_nonneg_right _ hLR.le
              exact (min_le_left _ _).trans (by linarith)
            · exact div_le_div_of_nonneg_right (min_le_right _ _) hLR.le
          have hqi : ∀ i ∈ A ℓ j, q i ≤ min (2 * P) 1 / L := by
            intro i hi
            have := hai i hi
            simp only [hq, cappedInclusion, if_neg hLne]
            split_ifs with h
            · apply div_le_div_of_nonneg_right _ hLR.le
              exact le_min (by linarith) (by linarith)
            · apply div_le_div_of_nonneg_right _ hLR.le
              rw [min_eq_right (by linarith)]
          set c := min (2 * P) 1 with hcdef
          have hc0 : 0 ≤ c := le_min (by linarith) zero_le_one
          have hc1 : c ≤ 1 := min_le_right _ _
          have hbase0 : 0 ≤ 1 - c / L := by rw [sub_nonneg, div_le_one hLR]; linarith
          have hbase1 : 1 - c / L ≤ 1 := by have := div_nonneg hc0 hLR.le; linarith
          have hcard : (A ℓ j).card ≤ L - 1 := by
            have h1 := List.toFinset_card_le (ℓ.take (ℓ.idxOf j))
            have h2 := List.length_take_le (ℓ.idxOf j) ℓ
            have h3 := List.idxOf_lt_length_of_mem hj
            have h4 := hlenL ℓ hℓ
            have h5 : (A ℓ j).card = (ℓ.take (ℓ.idxOf j)).toFinset.card := rfl
            omega
          have hprod : (1 - c / L) ^ (L - 1) ≤ ∏ i ∈ A ℓ j, (1 - q i) := by
            calc (1 - c / L) ^ (L - 1) ≤ (1 - c / L) ^ (A ℓ j).card :=
                  pow_le_pow_of_le_one hbase0 hbase1 hcard
              _ = ∏ i ∈ A ℓ j, (1 - c / L) := (Finset.prod_const _).symm
              _ ≤ _ := Finset.prod_le_prod (fun i _ => hbase0) (fun i hi => by linarith [hqi i hi])
          have hexp : Real.exp (-c) ≤ (1 - c / L) ^ (L - 1) := by
            rcases Nat.lt_or_ge L 2 with hL2 | hL2
            · have : L - 1 = 0 := by omega
              rw [this, pow_zero]; exact Real.exp_le_one_iff.mpr (by linarith)
            · have hm : ((L - 1 : ℕ) : ℝ) = (L:ℝ) - 1 := by
                rw [Nat.cast_sub (by omega)]; simp
              have hm1 : (1:ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
                rw [hm]; have : (2:ℝ) ≤ L := by exact_mod_cast hL2
                linarith
              set m : ℝ := ((L - 1 : ℕ) : ℝ) with hmdef
              have hy := Real.add_one_le_exp (c / m)
              have hmpos : 0 < m := by linarith
              have h1 : Real.exp (-(c / m)) ≤ 1 - c / L := by
                rw [Real.exp_neg]
                calc (Real.exp (c / m))⁻¹ ≤ (c / m + 1)⁻¹ :=
                      inv_anti₀ (by positivity) hy
                  _ = m / (c + m) := by field_simp
                  _ ≤ 1 - c / L := by
                    have hLm : (L:ℝ) = m + 1 := by rw [hm]; ring
                    rw [hLm, div_le_iff₀ (by positivity)]
                    rw [show (1 - c / (m + 1)) * (c + m) = (m + 1 - c) * (c + m) / (m + 1) by
                      field_simp]
                    rw [le_div_iff₀ (by positivity)]
                    nlinarith
              have h2 : Real.exp (-c) = Real.exp (-(c / m)) ^ (L - 1) := by
                rw [← Real.exp_nat_mul]; congr 1; rw [← hmdef]; field_simp
              rw [h2]
              exact pow_le_pow_left₀ (Real.exp_pos _).le h1 _
          have hfin : 2 * x ℓ j * Real.exp (-1) ≤ min (2 * x ℓ j) 1 * Real.exp (-c) := by
            rcases le_or_gt (2 * x ℓ j) 1 with h | h
            · rw [min_eq_left h]
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              exact Real.exp_le_exp.mpr (by linarith)
            · rw [min_eq_right h.le, one_mul]
              have hc : c = 2 * P := min_eq_left (by linarith)
              have := Real.add_one_le_exp (1 - c)
              have he : Real.exp (-c) = Real.exp (1 - c) * Real.exp (-1) := by
                rw [← Real.exp_add]; ring_nf
              rw [he]
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              linarith
          rw [lengthFactor, if_neg hLne]
          calc 2 / (Real.exp 1 * L) * x ℓ j = (2 * x ℓ j * Real.exp (-1)) / L := by
                rw [Real.exp_neg]; field_simp
            _ ≤ (min (2 * x ℓ j) 1 * Real.exp (-c)) / L := div_le_div_of_nonneg_right hfin hLR.le
            _ = (min (2 * x ℓ j) 1 / L) * Real.exp (-c) := by ring
            _ ≤ q j * ((1 - c / L) ^ (L - 1)) :=
                mul_le_mul hqj hexp (Real.exp_pos _).le (hqnn j)
            _ ≤ q j * ∏ i ∈ A ℓ j, (1 - q i) := mul_le_mul_of_nonneg_left hprod (hqnn j)
        let w : Finset (Fin n) → List (Fin n) → Fin n → ℝ := fun T ℓ j =>
          if j ∈ ℓ ∧ j ∈ T ∧ Disjoint (A ℓ j) T then (1:ℝ) else 0
        have hpt : ∀ T : Finset (Fin n),
            ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j, r j * w T ℓ j ≤ revAssort D r T := by
          intro T
          calc ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j, r j * w T ℓ j
              = ∑ ℓ ∈ D.supp, ∑ j ∈ T, D.p ℓ * (r j * w T ℓ j) := by
                apply Finset.sum_congr rfl; intro ℓ _; rw [Finset.mul_sum]
                symm; apply Finset.sum_subset (Finset.subset_univ T)
                intro j _ hjT; simp [w, hjT]
            _ ≤ ∑ ℓ ∈ D.supp, ∑ j ∈ T, r j * (if Chooses T ℓ j then D.p ℓ else 0) := by
                apply Finset.sum_le_sum; intro ℓ hℓ; apply Finset.sum_le_sum; intro j hjT
                by_cases hw : j ∈ ℓ ∧ j ∈ T ∧ Disjoint (A ℓ j) T
                · rw [if_pos (hchoose ℓ j T hw.1 hw.2.1 hw.2.2)]; simp only [w, if_pos hw]
                  ring_nf; exact le_refl _
                · simp only [w, if_neg hw, mul_zero]; apply mul_nonneg (hr j)
                  split_ifs
                  · exact (D.pos ℓ hℓ).le
                  · exact le_refl _
            _ = revAssort D r T := by
                unfold revAssort choiceProb
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro j _
                rw [Finset.sum_filter, Finset.mul_sum]
        have hswap : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                (∑ ℓ ∈ D.supp, D.p ℓ * ∑ j, r j * w T ℓ j) =
            ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j, r j * ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T * w T ℓ j := by
          simp only [Finset.mul_sum]
          conv_lhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro ℓ _
          conv_lhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro T _; ring
        have hinner : ∀ ℓ ∈ D.supp, ∑ j, r j * ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
              SpectralSparsify.Sampling.outcomeProb Finset.univ q T * w T ℓ j =
            ∑ j ∈ ℓ.toFinset, r j * (q j * ∏ i ∈ A ℓ j, (1 - q i)) := by
          intro ℓ hℓ
          rw [← Finset.sum_subset (Finset.subset_univ ℓ.toFinset)]
          · apply Finset.sum_congr rfl; intro j hj
            have hj' := List.mem_toFinset.mp hj
            rw [← hprob ℓ hℓ j hj']
            congr 1
            apply Finset.sum_congr rfl; intro T _
            simp only [w, hj', true_and]
          · intro j _ hj
            have hj' : j ∉ ℓ := fun h => hj (List.mem_toFinset.mpr h)
            simp [w, hj']
        calc lengthFactor L * revMech D r x
            = ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j ∈ ℓ.toFinset, r j * (lengthFactor L * x ℓ j) := by
              unfold revMech; rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro ℓ _
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
          _ ≤ ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j ∈ ℓ.toFinset, r j * (q j * ∏ i ∈ A ℓ j, (1 - q i)) :=
              Finset.sum_le_sum fun ℓ hℓ => mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
                  (hterm ℓ hℓ j (List.mem_toFinset.mp hj)) (hr j)) (D.pos ℓ hℓ).le
          _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
                SpectralSparsify.Sampling.outcomeProb Finset.univ q T *
                  (∑ ℓ ∈ D.supp, D.p ℓ * ∑ j, r j * w T ℓ j) := by
              rw [hswap]
              apply Finset.sum_congr rfl; intro ℓ hℓ
              rw [hinner ℓ hℓ]
          _ ≤ revIndependent D r q := by
              unfold revIndependent SpectralSparsify.Sampling.expect
              exact Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hpt T) (hoP T)
