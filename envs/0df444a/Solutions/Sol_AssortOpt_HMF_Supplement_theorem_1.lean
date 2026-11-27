-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:50.2452+00:00
-- url     : https://prove2.me/submissions/1903633b-d9b5-4929-9a04-88919ac8cd7b

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_MarkovModel

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution {n : ℕ} (C : MarkovModel n) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n),
      IsGreatest (revMech (inducedDist C) r '' {x | IsIC (inducedDist C) x})
        (revAssort (inducedDist C) r S) := by
          classical
          set D := inducedDist C with hD
          set H : Finset (Fin n) → List (Fin n) → ℝ := fun T t =>
            ∑ x ∈ T, r x * if List.find? (fun i => decide (i ∈ T)) t = some x then 1 else 0 with hH
          set val : Finset (Fin n) → Fin n → ℝ := fun T i =>
            ∑' σ, walkTail C.chain i σ * H T (i :: σ) with hval
          obtain ⟨S, -, hS⟩ := Finset.exists_max_image Finset.univ (fun T => ∑ i, val T i)
            Finset.univ_nonempty
          -- sum of a choice indicator over a finset
          have huniq : ∀ ℓ j j', Chooses S ℓ j → Chooses S ℓ j' → j = j' := by
            intro ℓ j j' h h'
            unfold Chooses at h h'
            rw [h] at h'; exact Option.some.inj h'
          have hmemC : ∀ ℓ j, Chooses S ℓ j → j ∈ ℓ ∧ j ∈ S := by
            intro ℓ j h
            unfold Chooses at h
            exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
          have hsumInd : ∀ (ℓ : List (Fin n)) (A : Finset (Fin n)),
              ∑ j ∈ A, assortMech S ℓ j =
                if ∃ j0 ∈ A, Chooses S ℓ j0 then 1 else 0 := by
            intro ℓ A
            split_ifs with h
            · obtain ⟨j0, hj0, hc⟩ := h
              rw [Finset.sum_eq_single j0]
              · simp [assortMech, hc]
              · intro j _ hne
                simp only [assortMech]
                rw [if_neg]
                intro hc'; exact hne (huniq _ _ _ hc' hc)
              · intro h; exact absurd hj0 h
            · apply Finset.sum_eq_zero
              intro j hj
              simp only [assortMech]
              rw [if_neg]
              intro hc; exact h ⟨j, hj, hc⟩
          have hIC : IsIC D (assortMech S) := by
            refine ⟨?_, ?_, ?_⟩
            · intro ℓ _ k _ ℓ' _
              rw [hsumInd, hsumInd]
              split_ifs with h1 h2
              · exact le_refl _
              · exfalso
                obtain ⟨j0, hj0, hf⟩ := h1
                rw [Finset.mem_inter, List.mem_toFinset] at hj0
                have hS0 : j0 ∈ S := (hmemC _ _ hf).2
                have hsome : ((ℓ.take k).find? (fun i => decide (i ∈ S))).isSome := by
                  rw [List.find?_isSome]; exact ⟨j0, hj0.1, by simpa using hS0⟩
                obtain ⟨j1, hj1⟩ := Option.isSome_iff_exists.mp hsome
                apply h2
                refine ⟨j1, List.mem_toFinset.mpr (List.mem_of_find?_eq_some hj1), ?_⟩
                show ℓ.find? _ = _
                rw [← List.take_append_drop k ℓ, List.find?_append, hj1]
                rfl
              · norm_num
              · exact le_refl _
            · intro ℓ _
              rw [hsumInd]; split_ifs <;> norm_num
            · intro ℓ _ j _
              unfold assortMech; split_ifs <;> norm_num
          have hRev : revMech D r (assortMech S) = revAssort D r S := by
            unfold revMech revAssort choiceProb
            simp_rw [Finset.sum_filter, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro ℓ _
            have h1 : ∑ j ∈ ℓ.toFinset, D.p ℓ * (r j * assortMech S ℓ j) =
                ∑ j, D.p ℓ * (r j * assortMech S ℓ j) := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro j _ hj
              simp only [assortMech]
              rw [if_neg]; · ring
              intro h; exact hj (List.mem_toFinset.mpr (hmemC _ _ h).1)
            have h2 : ∑ j ∈ S, (if Chooses S ℓ j then r j * D.p ℓ else 0) =
                ∑ j, D.p ℓ * (r j * assortMech S ℓ j) := by
              apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
              · intro j hj
                rw [Finset.mem_sdiff] at hj
                simp only [assortMech]
                rw [if_neg]; · ring
                intro h; exact hj.2 (hmemC _ _ h).2
              · intro j _
                unfold assortMech
                split_ifs <;> ring
            rw [h1, ← h2]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> ring
          refine ⟨S, ⟨assortMech S, hIC, hRev⟩, ?_⟩
          rintro _ ⟨x, hx, rfl⟩
          -- Step 1: an IC mechanism earns the revenue of its increasing set function `maxMass`.
          have hred : revMech D r x = revSetFn D r (maxMass D.supp x) := by
            unfold revMech revSetFn
            obtain ⟨hx1, hx2, hx3⟩ := hx
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            congr 1
            have hnd := D.nodup ℓ hℓ
            have hF : ∀ k ≤ ℓ.length, maxMass D.supp x (ℓ.take k).toFinset =
                ∑ j ∈ (ℓ.take k).toFinset, x ℓ j := by
              intro k hk
              unfold maxMass
              apply le_antisymm
              · apply Finset.max'_le
                intro y hy
                rw [Finset.mem_insert, Finset.mem_image] at hy
                rcases hy with rfl | ⟨ℓ', hℓ', rfl⟩
                · apply Finset.sum_nonneg
                  intro j hj
                  exact hx3 ℓ hℓ j (List.mem_of_mem_take (List.mem_toFinset.mp hj))
                · exact hx1 ℓ hℓ k hk ℓ' hℓ'
              · apply Finset.le_max'
                apply Finset.mem_insert_of_mem
                rw [Finset.mem_image]
                refine ⟨ℓ, hℓ, ?_⟩
                rw [Finset.inter_eq_left.mpr]
                intro j hj
                exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hj))
            rw [List.sum_toFinset _ hnd, ← Fin.sum_univ_fun_getElem]
            apply Finset.sum_congr rfl
            intro k _
            have hk := k.isLt
            rw [hF (k + 1) (by omega), hF k (by omega)]
            have hins : (ℓ.take (k+1)).toFinset = insert (ℓ[(k:ℕ)]) (ℓ.take k).toFinset := by
              simp only [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
                List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
              ext a; simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
              exact or_comm
            have hnot : ℓ[(k:ℕ)] ∉ (ℓ.take k).toFinset := by
              rw [List.mem_toFinset]
              intro hm
              obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hm
              rw [List.getElem_take] at hie
              have hi' : i < k := by simpa using hi
              have := (List.Nodup.getElem_inj_iff hnd).mp hie
              omega
            rw [hins, Finset.sum_insert hnot]
            simp
          rw [hred]
          set w : List (Fin n) → ℝ := walkWeight C.chain C.initial with hw
          have htail_nn : ∀ t i, 0 ≤ walkTail C.chain i t := by
            intro t
            induction t with
            | nil => intro i; exact C.chain.nonneg _ _
            | cons j t ih => intro i; exact mul_nonneg (C.chain.nonneg _ _) (ih j)
          have hrow : ∀ j : Fin n, C.chain.P (some j) none + ∑ k : Fin n, C.chain.P (some j) (some k) = 1 := by
            intro j
            have := C.chain.row_sum (some j)
            rwa [Fintype.sum_option] at this
          have htail_fin : ∀ L : ℕ, ∀ (s : Finset (List (Fin n))), (∀ σ ∈ s, σ.length ≤ L) →
              ∀ j, ∑ σ ∈ s, walkTail C.chain j σ ≤ 1 := by
            intro L
            induction L with
            | zero =>
              intro s hs j
              have : s ⊆ {[]} := by
                intro σ hσ; rw [Finset.mem_singleton]; exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hs σ hσ))
              calc ∑ σ ∈ s, walkTail C.chain j σ ≤ ∑ σ ∈ ({[]} : Finset (List (Fin n))), walkTail C.chain j σ :=
                    Finset.sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => htail_nn _ _)
                _ ≤ 1 := by
                  simp only [Finset.sum_singleton, walkTail]
                  have := hrow j
                  have h2 : 0 ≤ ∑ k : Fin n, C.chain.P (some j) (some k) :=
                    Finset.sum_nonneg (fun _ _ => C.chain.nonneg _ _)
                  linarith
            | succ L ih =>
              intro s hs j
              have hsplit : ∑ σ ∈ s, walkTail C.chain j σ ≤
                  walkTail C.chain j [] + ∑ k : Fin n, ∑ τ ∈ (s.filter (fun σ => σ.head? = some k)).image List.tail,
                    walkTail C.chain j (k :: τ) := by
                have h1 : ∑ σ ∈ s, walkTail C.chain j σ =
                    ∑ σ ∈ s.filter (fun σ => σ = []), walkTail C.chain j σ +
                    ∑ σ ∈ s.filter (fun σ => σ ≠ []), walkTail C.chain j σ :=
                  (Finset.sum_filter_add_sum_filter_not s _ _).symm
                have h2 : ∑ σ ∈ s.filter (fun σ => σ = []), walkTail C.chain j σ ≤ walkTail C.chain j [] := by
                  calc _ ≤ ∑ σ ∈ ({[]} : Finset (List (Fin n))), walkTail C.chain j σ := by
                        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => htail_nn _ _)
                        intro σ hσ; rw [Finset.mem_filter] at hσ; rw [Finset.mem_singleton]; exact hσ.2
                    _ = _ := Finset.sum_singleton _ _
                have h3 : ∑ σ ∈ s.filter (fun σ => σ ≠ []), walkTail C.chain j σ =
                    ∑ k : Fin n, ∑ σ ∈ s.filter (fun σ => σ.head? = some k), walkTail C.chain j σ := by
                  rw [← Finset.sum_biUnion]
                  · apply Finset.sum_congr _ (fun _ _ => rfl)
                    ext σ
                    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
                    constructor
                    · rintro ⟨h, hne⟩
                      obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
                      exact ⟨a, h, rfl⟩
                    · rintro ⟨a, h, ha⟩
                      refine ⟨h, ?_⟩
                      rintro rfl; simp at ha
                  · intro a _ b _ hab
                    simp only [Function.onFun]
                    rw [Finset.disjoint_left]
                    intro σ h1 h2
                    rw [Finset.mem_filter] at h1 h2
                    exact hab (Option.some.inj (h1.2.symm.trans h2.2))
                have h4 : ∀ k : Fin n, ∑ σ ∈ s.filter (fun σ => σ.head? = some k), walkTail C.chain j σ =
                    ∑ τ ∈ (s.filter (fun σ => σ.head? = some k)).image List.tail, walkTail C.chain j (k :: τ) := by
                  intro k
                  rw [Finset.sum_image]
                  · apply Finset.sum_congr rfl
                    intro σ hσ
                    rw [Finset.mem_filter] at hσ
                    cases σ with
                    | nil => simp at hσ
                    | cons a l =>
                      simp only [List.head?_cons, Option.some.injEq] at hσ
                      rw [hσ.2]; rfl
                  · intro x hx y hy hxy
                    rw [Finset.coe_filter] at hx hy
                    simp only [Set.mem_setOf_eq] at hx hy
                    cases x with
                    | nil => simp at hx
                    | cons a l =>
                      cases y with
                      | nil => simp at hy
                      | cons b m =>
                        simp only [List.head?_cons, Option.some.injEq] at hx hy
                        simp only [List.tail_cons] at hxy
                        rw [hx.2, hy.2, hxy]
                rw [h1, h3]
                simp_rw [h4]
                linarith
              refine le_trans hsplit ?_
              have h5 : ∀ k : Fin n, ∑ τ ∈ (s.filter (fun σ => σ.head? = some k)).image List.tail,
                  walkTail C.chain j (k :: τ) ≤ C.chain.P (some j) (some k) := by
                intro k
                simp only [walkTail]
                rw [← Finset.mul_sum]
                apply mul_le_of_le_one_right (C.chain.nonneg _ _)
                apply ih
                intro τ hτ
                rw [Finset.mem_image] at hτ
                obtain ⟨σ, hσ, rfl⟩ := hτ
                have := hs σ (Finset.mem_filter.mp hσ).1
                rw [List.length_tail]; omega
              calc _ ≤ walkTail C.chain j [] + ∑ k : Fin n, C.chain.P (some j) (some k) :=
                    by gcongr with k; exact h5 k
                _ = 1 := hrow j
          have htail_le : ∀ j (s : Finset (List (Fin n))), ∑ σ ∈ s, walkTail C.chain j σ ≤ 1 := by
            intro j s
            exact htail_fin (s.sup List.length) s (fun σ hσ => Finset.le_sup (f := List.length) hσ) j
          have htail_summ : ∀ j, Summable (walkTail C.chain j) := by
            intro j
            exact summable_of_sum_le (fun σ => htail_nn σ j) (htail_le j)
          have htail_tsum : ∀ j, ∑' σ, walkTail C.chain j σ ≤ 1 := by
            intro j
            exact Summable.tsum_le_of_sum_le (htail_summ j) (htail_le j)
          have hstep : ∀ (j : Fin n) (G : List (Fin n) → ℝ) (B : ℝ), (∀ t, |G t| ≤ B) → G [] = 0 →
              ∑' σ, walkTail C.chain j σ * G σ =
                ∑ k : Fin n, C.chain.P (some j) (some k) * ∑' σ, walkTail C.chain k σ * G (k :: σ) := by
            intro j G B hB h0
            have hsum : Summable (fun σ => walkTail C.chain j σ * G σ) := by
              apply Summable.of_norm_bounded (g := fun σ => walkTail C.chain j σ * B) ((htail_summ j).mul_right B)
              intro σ
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (htail_nn _ _)]
              exact mul_le_mul_of_nonneg_left (hB _) (htail_nn _ _)
            have hinj : Function.Injective (fun p : Fin n × List (Fin n) => p.1 :: p.2) := by
              rintro ⟨a, l⟩ ⟨b, m⟩ h
              simp only [List.cons.injEq] at h
              rw [h.1, h.2]
            rw [← hinj.tsum_eq (f := fun σ => walkTail C.chain j σ * G σ)]
            · rw [Summable.tsum_prod (f := fun c : Fin n × List (Fin n) =>
                walkTail C.chain j (c.1 :: c.2) * G (c.1 :: c.2)) (hsum.comp_injective hinj), tsum_fintype]
              apply Finset.sum_congr rfl
              intro k _
              rw [← tsum_mul_left]
              apply tsum_congr; intro σ
              simp only [walkTail]; ring
            · intro t ht
              cases t with
              | nil => exfalso; apply ht; simp [h0]
              | cons a l => exact ⟨(a, l), rfl⟩
          set pw : List (Fin n) → Fin n → Fin n → ℝ := fun u => List.rec (motive := fun _ => Fin n → Fin n → ℝ)
            (fun j i => C.chain.P (some i) (some j)) (fun k _ ih j i => C.chain.P (some i) (some k) * ih j k) u
            with hpw
          have hpw_split : ∀ (u : List (Fin n)) (j i : Fin n) (σ : List (Fin n)),
              walkTail C.chain i (u ++ j :: σ) = pw u j i * walkTail C.chain j σ := by
            intro u
            induction u with
            | nil => intro j i σ; rfl
            | cons k u ih =>
              intro j i σ
              show C.chain.P (some i) (some k) * walkTail C.chain k (u ++ j :: σ) =
                C.chain.P (some i) (some k) * pw u j k * walkTail C.chain j σ
              rw [ih, mul_assoc]
          have hpw_nn : ∀ u j i, 0 ≤ pw u j i := by
            intro u
            induction u with
            | nil => intro j i; exact C.chain.nonneg _ _
            | cons k u ih => intro j i; exact mul_nonneg (C.chain.nonneg _ _) (ih j k)
          have hhit : ∀ (U : Finset (Fin n)) (j i : Fin n), j ∈ U → ∀ (G : List (Fin n) → ℝ) (B : ℝ),
              (∀ t, |G t| ≤ B) →
              ∑' σ, walkTail C.chain i σ * (if σ.find? (fun x => decide (x ∈ U)) = some j then
                  G (σ.dropWhile (fun x => !decide (x ∈ U))).tail else 0) =
                (∑' u : {u : List (Fin n) // ∀ x ∈ u, x ∉ U}, pw u.1 j i) *
                  ∑' σ, walkTail C.chain j σ * G σ := by
            intro U j i hj G B hB
            set f : List (Fin n) → ℝ := fun σ => walkTail C.chain i σ *
              (if σ.find? (fun x => decide (x ∈ U)) = some j then
                  G (σ.dropWhile (fun x => !decide (x ∈ U))).tail else 0) with hf
            have hfsum : Summable f := by
              apply Summable.of_norm_bounded (g := fun σ => walkTail C.chain i σ * B) ((htail_summ i).mul_right B)
              intro σ
              rw [hf]; dsimp only
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (htail_nn _ _)]
              apply mul_le_mul_of_nonneg_left _ (htail_nn _ _)
              split_ifs
              · exact hB _
              · simpa using (abs_nonneg _).trans (hB [])
            set g : {u : List (Fin n) // ∀ x ∈ u, x ∉ U} × List (Fin n) → List (Fin n) :=
              fun p => p.1.1 ++ j :: p.2 with hg
            have hfg : ∀ p, f (g p) = pw p.1.1 j i * (walkTail C.chain j p.2 * G p.2) := by
              rintro ⟨⟨u, hu⟩, σ⟩
              rw [hf, hg]; dsimp only
              have h1 : (u ++ j :: σ).find? (fun x => decide (x ∈ U)) = some j := by
                rw [List.find?_eq_some_iff_append]
                exact ⟨by simpa using hj, u, σ, rfl, fun a ha => by simpa using hu a ha⟩
              have h2 : (u ++ j :: σ).dropWhile (fun x => !decide (x ∈ U)) = j :: σ := by
                rw [List.dropWhile_append_of_pos (fun a ha => by simpa using hu a ha)]
                simp [hj]
              rw [if_pos h1, h2, List.tail_cons, hpw_split]; ring
            have hginj : Function.Injective g := by
              rintro ⟨⟨u, hu⟩, σ⟩ ⟨⟨v, hv⟩, τ⟩ h
              rw [hg] at h; dsimp only at h
              have h1 : (u ++ j :: σ).dropWhile (fun x => !decide (x ∈ U)) = j :: σ := by
                rw [List.dropWhile_append_of_pos (fun a ha => by simpa using hu a ha)]
                simp [hj]
              have h2 : (v ++ j :: τ).dropWhile (fun x => !decide (x ∈ U)) = j :: τ := by
                rw [List.dropWhile_append_of_pos (fun a ha => by simpa using hv a ha)]
                simp [hj]
              have hστ : σ = τ := by
                have := h1.symm.trans (h ▸ h2); simpa using this
              subst hστ
              have : u = v := List.append_cancel_right h
              subst this
              rfl
            rw [← hginj.tsum_eq (f := f)]
            · rw [Summable.tsum_prod (f := fun c => f (g c)) (hfsum.comp_injective hginj)]
              simp_rw [hfg, tsum_mul_left]
              exact tsum_mul_right
            · intro σ hσ
              rw [Function.mem_support, hf] at hσ
              dsimp only at hσ
              by_cases h : σ.find? (fun x => decide (x ∈ U)) = some j
              · obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.mp h
                exact ⟨(⟨as, fun a ha => by simpa using has a ha⟩, bs), rfl⟩
              · exfalso; apply hσ; rw [if_neg h, mul_zero]
          have hw_nn : ∀ t, 0 ≤ w t := by
            intro t; cases t with
            | nil => exact C.initial_nonneg _
            | cons i t => exact mul_nonneg (C.initial_nonneg _) (htail_nn t i)
          have hwalks : ∀ t, C.walks t = ENNReal.ofReal (w t) := C.walks_eq
          have hw_summ : Summable w := by
            have h := ENNReal.summable_toReal (f := C.walks) (by rw [PMF.tsum_coe]; simp)
            simpa [hwalks, ENNReal.toReal_ofReal (hw_nn _)] using h
          have hw_sum : ∑' t, w t = 1 := by
            have h := ENNReal.tsum_toReal_eq (f := C.walks) (fun a => PMF.apply_ne_top _ a)
            rw [PMF.tsum_coe] at h
            simpa [hwalks, ENNReal.toReal_ofReal (hw_nn _)] using h.symm
          have hfirst : ∀ (G : List (Fin n) → ℝ) (B : ℝ), (∀ t, |G t| ≤ B) → G [] = 0 →
              ∑' t, w t * G t =
                ∑ k : Fin n, C.initial (some k) * ∑' σ, walkTail C.chain k σ * G (k :: σ) := by
            intro G B hB h0
            have hsum : Summable (fun σ => w σ * G σ) := by
              apply Summable.of_norm_bounded (g := fun σ => w σ * B) (hw_summ.mul_right B)
              intro σ
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw_nn _)]
              exact mul_le_mul_of_nonneg_left (hB _) (hw_nn _)
            have hinj : Function.Injective (fun p : Fin n × List (Fin n) => p.1 :: p.2) := by
              rintro ⟨a, l⟩ ⟨b, m⟩ h
              simp only [List.cons.injEq] at h
              rw [h.1, h.2]
            rw [← hinj.tsum_eq (f := fun σ => w σ * G σ)]
            · rw [Summable.tsum_prod (f := fun c : Fin n × List (Fin n) =>
                w (c.1 :: c.2) * G (c.1 :: c.2)) (hsum.comp_injective hinj), tsum_fintype]
              apply Finset.sum_congr rfl
              intro k _
              rw [← tsum_mul_left]
              apply tsum_congr; intro σ
              simp only [hw, walkWeight]; ring
            · intro t ht
              cases t with
              | nil => exfalso; apply ht; simp [h0]
              | cons a l => exact ⟨(a, l), rfl⟩
          have hlaw : ∀ a : Report n, ((listLaw C) a).toReal = ∑' t, if a = firstVisits t then w t else 0 := by
            intro a
            unfold listLaw
            rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
            · congr 1; ext t; split_ifs <;> simp [hwalks, ENNReal.toReal_ofReal (hw_nn _)]
            · intro t; split_ifs <;> simp [hwalks]
          have hsuppD : D.supp = (allReports n).filter (fun ℓ => 0 < reportProb (listLaw C) ℓ) := rfl
          have hpD : D.p = reportProb (listLaw C) := rfl
          have hwalk : ∀ φ : List (Fin n) → ℝ,
              ∑ ℓ ∈ D.supp, D.p ℓ * φ ℓ = ∑' t, w t * φ (firstVisits t).val := by
            intro φ
            set B := ∑ a : Report n, |φ a.val| with hBdef
            have hB : ∀ a : Report n, |φ a.val| ≤ B := fun a =>
              Finset.single_le_sum (f := fun a : Report n => |φ a.val|) (fun _ _ => abs_nonneg _)
                (Finset.mem_univ a)
            have hp_nn : ∀ ℓ, 0 ≤ reportProb (listLaw C) ℓ := by
              intro ℓ; unfold reportProb; split <;> positivity
            rw [hsuppD, hpD]
            have h1 : ∑ ℓ ∈ (allReports n).filter (fun ℓ => 0 < reportProb (listLaw C) ℓ),
                reportProb (listLaw C) ℓ * φ ℓ = ∑ ℓ ∈ allReports n, reportProb (listLaw C) ℓ * φ ℓ := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro ℓ hA h
              have : reportProb (listLaw C) ℓ = 0 :=
                le_antisymm (le_of_not_gt fun hpos => h (Finset.mem_filter.mpr ⟨hA, hpos⟩)) (hp_nn ℓ)
              simp [this]
            rw [h1]
            unfold allReports
            rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
            have h2 : ∀ a : Report n, reportProb (listLaw C) a.val * φ a.val =
                ∑' t, (if a = firstVisits t then w t else 0) * φ a.val := by
              intro a
              rw [tsum_mul_right, ← hlaw]
              simp [reportProb, a.property]
            simp_rw [h2]
            rw [← Summable.tsum_finsetSum]
            · congr 1; ext t
              rw [Finset.sum_eq_single (firstVisits t)]
              · simp
              · intro b _ hb; simp [hb]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro a _
              apply Summable.of_norm_bounded (g := fun t => w t * B)
              · exact hw_summ.mul_right B
              · intro t
                split_ifs
                · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw_nn t)]
                  exact mul_le_mul_of_nonneg_left (hB _) (hw_nn t)
                · simp; exact mul_nonneg (hw_nn t) ((abs_nonneg _).trans (hB ⟨[], List.nodup_nil⟩))
          rw [revSetFn, revAssort]
          have hA : ∑ j ∈ S, r j * choiceProb D S j =
              ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j ∈ S, r j * assortMech S ℓ j := by
            unfold choiceProb
            simp_rw [Finset.sum_filter, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro ℓ _
            apply Finset.sum_congr rfl; intro j _
            unfold assortMech; split_ifs <;> ring
          rw [hA, hwalk, hwalk]
          -- Step 2 (open): for the first-visit law of a Markov chain, the revenue of any increasing
          -- set function is at most that of the revenue-maximizing assortment `S`.
          -- the increasing set function of `x`: nonnegative, monotone, at most one, zero at ∅
          set F := maxMass D.supp x with hFdef
          obtain ⟨hx1, hx2, hx3⟩ := hx
          have hF_nn : ∀ A, 0 ≤ F A := fun A =>
            Finset.le_max' _ _ (Finset.mem_insert_self _ _)
          have hF_mono : ∀ A B : Finset (Fin n), A ⊆ B → F A ≤ F B := by
            intro A B hAB
            apply Finset.max'_le
            intro y hy
            rw [Finset.mem_insert, Finset.mem_image] at hy
            rcases hy with rfl | ⟨ℓ, hℓ, rfl⟩
            · exact hF_nn B
            · refine le_trans ?_ (Finset.le_max' _ _ (Finset.mem_insert_of_mem
                (Finset.mem_image_of_mem _ hℓ)))
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_inter_right hAB)
              intro j hj _
              exact hx3 ℓ hℓ j (List.mem_toFinset.mp (Finset.mem_inter.mp hj).2)
          have hF_le : ∀ A, F A ≤ 1 := by
            intro A
            apply Finset.max'_le
            intro y hy
            rw [Finset.mem_insert, Finset.mem_image] at hy
            rcases hy with rfl | ⟨ℓ, hℓ, rfl⟩
            · norm_num
            · refine le_trans ?_ (hx2 ℓ hℓ)
              apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              intro j hj _
              exact hx3 ℓ hℓ j (List.mem_toFinset.mp hj)
          have hF_empty : F ∅ = 0 := by
            apply le_antisymm _ (hF_nn _)
            apply Finset.max'_le
            intro y hy
            rw [Finset.mem_insert, Finset.mem_image] at hy
            rcases hy with rfl | ⟨ℓ, hℓ, rfl⟩
            · exact le_refl _
            · simp
          -- walk weights factor along a prefix (Markov property)
          have hfind : ∀ (p : Fin n → Bool) (t : List (Fin n)), (firstVisits t).val.find? p = t.find? p := by
            intro p t
            show (t.reverse.dedup.reverse).find? p = t.find? p
            induction t using List.reverseRecOn with
            | nil => simp
            | append_singleton l a ih =>
              rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.dedup_cons]
              split_ifs with ha
              · rw [ih, List.find?_append]
                rw [List.mem_reverse] at ha
                cases hf : l.find? p with
                | some b => simp
                | none =>
                  rw [List.find?_eq_none] at hf
                  simp [hf a ha]
              · rw [List.reverse_cons, List.find?_append, List.find?_append, ih]
          set R : List (Fin n) → ℝ := fun l => ∑ s ∈ Finset.range l.length,
            (l[s]?.elim 0 r) * (F (l.take (s+1)).toFinset - F (l.take s).toFinset) with hR
          have hRfin : ∀ l : List (Fin n), ∑ k : Fin l.length, r (l.get k) *
              (F (l.take (k+1)).toFinset - F (l.take k).toFinset) = R l := by
            intro l
            show _ = ∑ s ∈ Finset.range l.length,
              (l[s]?.elim 0 r) * (F (l.take (s+1)).toFinset - F (l.take s).toFinset)
            rw [← Fin.sum_univ_eq_sum_range (fun s => (l[s]?.elim 0 r) * (F (l.take (s+1)).toFinset - F (l.take s).toFinset))]
            apply Finset.sum_congr rfl
            intro k _
            simp
          have hRsnoc : ∀ (l : List (Fin n)) (a : Fin n),
              R (l ++ [a]) = R l + r a * (F (l ++ [a]).toFinset - F l.toFinset) := by
            intro l a
            simp only [hR]
            rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
            congr 1
            · apply Finset.sum_congr rfl
              intro s hs
              rw [Finset.mem_range] at hs
              rw [List.getElem?_append_left hs, List.take_append_of_le_length (by omega),
                List.take_append_of_le_length (by omega)]
            · rw [List.getElem?_append_right (le_refl _), List.take_of_length_le (by simp),
                List.take_append_of_le_length (le_refl _), List.take_length]
              simp
          have hfvsnoc : ∀ (l : List (Fin n)) (a : Fin n),
              (firstVisits (l ++ [a])).val = if a ∈ l then (firstVisits l).val else (firstVisits l).val ++ [a] := by
            intro l a
            show (l ++ [a]).reverse.dedup.reverse = _
            rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.dedup_cons]
            split_ifs with h1 h2 h2
            · rfl
            · exact absurd (List.mem_reverse.mp h1) h2
            · exact absurd (List.mem_reverse.mpr h2) h1
            · rw [List.reverse_cons]; rfl
          have hfvset : ∀ l : List (Fin n), (firstVisits l).val.toFinset = l.toFinset := by
            intro l; ext a
            simp [firstVisits]
          have hRfv : ∀ t : List (Fin n), R (firstVisits t).val = R t := by
            intro t
            induction t using List.reverseRecOn with
            | nil => rfl
            | append_singleton l a ih =>
              rw [hfvsnoc, hRsnoc l a]
              split_ifs with ha
              · rw [ih]
                have : (l ++ [a]).toFinset = l.toFinset := by
                  ext b; simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
                  constructor
                  · rintro (h | rfl) <;> assumption
                  · exact Or.inl
                rw [this]; ring
              · rw [hRsnoc, ih]
                rw [hfvset]
                have : ((firstVisits l).val ++ [a]).toFinset = (l ++ [a]).toFinset := by
                  ext b; simp [hfvset]
                rw [this]
          simp_rw [hRfin, hRfv]
          simp only [assortMech, Chooses, hfind]
          set Rs : ℝ := ∑ j, r j with hRs
          have hr_le : ∀ j, r j ≤ Rs := fun j =>
            Finset.single_le_sum (f := r) (fun i _ => hr i) (Finset.mem_univ j)
          have hHfind : ∀ T t, H T t = (t.find? (fun x => decide (x ∈ T))).elim 0 r := by
            intro T t
            rw [hH]; dsimp only
            cases hf : t.find? (fun x => decide (x ∈ T)) with
            | none => simp
            | some j =>
              have hjT : j ∈ T := by simpa using List.find?_some hf
              rw [Finset.sum_eq_single j]
              · simp
              · intro b _ hb; simp [Ne.symm hb]
              · intro h; exact absurd hjT h
          have hH0 : ∀ T, H T [] = 0 := by intro T; rw [hHfind]; rfl
          have hHnn : ∀ T t, 0 ≤ H T t := by
            intro T t; rw [hHfind]; cases t.find? (fun x => decide (x ∈ T)) with
            | none => exact le_refl _
            | some j => exact hr j
          have hHle : ∀ T t, H T t ≤ Rs := by
            intro T t; rw [hHfind]; cases t.find? (fun x => decide (x ∈ T)) with
            | none => exact Finset.sum_nonneg (fun i _ => hr i)
            | some j => exact hr_le j
          have hHabs : ∀ T t, |H T t| ≤ Rs := fun T t => by
            rw [abs_of_nonneg (hHnn T t)]; exact hHle T t
          have hHmem : ∀ T i σ, i ∈ T → H T (i :: σ) = r i := by
            intro T i σ hi; rw [hHfind]; simp [List.find?_cons, hi]
          have hHnot : ∀ T i σ, i ∉ T → H T (i :: σ) = H T σ := by
            intro T i σ hi; rw [hHfind, hHfind]; simp [List.find?_cons, hi]
          have hP : ∀ T j, j ∈ T → ∀ σ, H T σ - H (T.erase j) σ =
              if σ.find? (fun x => decide (x ∈ T)) = some j then
                r j - H (T.erase j) (σ.dropWhile (fun x => !decide (x ∈ T))).tail else 0 := by
            intro T j hj σ
            induction σ with
            | nil => simp [hH0]
            | cons a σ ih =>
              by_cases ha : a = j
              · subst ha
                rw [hHmem _ _ _ hj, hHnot _ _ _ (by simp)]
                simp [List.find?_cons, hj]
              · by_cases haT : a ∈ T
                · rw [hHmem _ _ _ haT, hHmem _ _ _ (Finset.mem_erase.mpr ⟨ha, haT⟩)]
                  simp [List.find?_cons, haT, ha]
                · rw [hHnot _ _ _ haT, hHnot _ _ _ (fun h => haT (Finset.mem_of_mem_erase h)), ih]
                  simp [List.find?_cons, haT]
          have hpw_fin : ∀ (j : Fin n) (L : ℕ) (s : Finset (List (Fin n))),
              (∀ u ∈ s, u.length ≤ L ∧ j ∉ u) → ∀ i, ∑ u ∈ s, pw u j i ≤ 1 := by
            intro j L
            induction L with
            | zero =>
              intro s hs i
              have : s ⊆ {[]} := by
                intro σ hσ; rw [Finset.mem_singleton]; exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hs σ hσ).1)
              calc ∑ u ∈ s, pw u j i ≤ ∑ u ∈ ({[]} : Finset (List (Fin n))), pw u j i :=
                    Finset.sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => hpw_nn _ _ _)
                _ ≤ 1 := by
                  simp only [Finset.sum_singleton]
                  show C.chain.P (some i) (some j) ≤ 1
                  have := hrow i
                  have h2 : C.chain.P (some i) (some j) ≤ ∑ k : Fin n, C.chain.P (some i) (some k) :=
                    Finset.single_le_sum (f := fun k => C.chain.P (some i) (some k))
                      (fun _ _ => C.chain.nonneg _ _) (Finset.mem_univ j)
                  have := C.chain.nonneg (some i) none
                  linarith
            | succ L ih =>
              intro s hs i
              have h1 : ∑ σ ∈ s, pw σ j i =
                  ∑ σ ∈ s.filter (fun σ => σ = []), pw σ j i +
                  ∑ σ ∈ s.filter (fun σ => σ ≠ []), pw σ j i :=
                (Finset.sum_filter_add_sum_filter_not s _ _).symm
              have h2 : ∑ σ ∈ s.filter (fun σ => σ = []), pw σ j i ≤ C.chain.P (some i) (some j) := by
                calc _ ≤ ∑ σ ∈ ({[]} : Finset (List (Fin n))), pw σ j i := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => hpw_nn _ _ _)
                      intro σ hσ; rw [Finset.mem_filter] at hσ; rw [Finset.mem_singleton]; exact hσ.2
                  _ = _ := Finset.sum_singleton _ _
              have h3 : ∑ σ ∈ s.filter (fun σ => σ ≠ []), pw σ j i =
                  ∑ k : Fin n, ∑ σ ∈ s.filter (fun σ => σ.head? = some k), pw σ j i := by
                rw [← Finset.sum_biUnion]
                · apply Finset.sum_congr _ (fun _ _ => rfl)
                  ext σ
                  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
                  constructor
                  · rintro ⟨h, hne⟩
                    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
                    exact ⟨a, h, rfl⟩
                  · rintro ⟨a, h, ha⟩
                    refine ⟨h, ?_⟩
                    rintro rfl; simp at ha
                · intro a _ b _ hab
                  simp only [Function.onFun]
                  rw [Finset.disjoint_left]
                  intro σ h1 h2
                  rw [Finset.mem_filter] at h1 h2
                  exact hab (Option.some.inj (h1.2.symm.trans h2.2))
              have h4 : ∀ k : Fin n, ∑ σ ∈ s.filter (fun σ => σ.head? = some k), pw σ j i ≤
                  if k = j then 0 else C.chain.P (some i) (some k) := by
                intro k
                split_ifs with hk
                · apply le_of_eq
                  apply Finset.sum_eq_zero
                  intro σ hσ
                  rw [Finset.mem_filter] at hσ
                  exfalso
                  cases σ with
                  | nil => simp at hσ
                  | cons a l =>
                    simp only [List.head?_cons, Option.some.injEq] at hσ
                    exact (hs _ hσ.1).2 (by rw [hσ.2, hk]; exact List.mem_cons_self)
                · have e : ∑ σ ∈ s.filter (fun σ => σ.head? = some k), pw σ j i =
                      ∑ τ ∈ (s.filter (fun σ => σ.head? = some k)).image List.tail,
                        C.chain.P (some i) (some k) * pw τ j k := by
                    rw [Finset.sum_image]
                    · apply Finset.sum_congr rfl
                      intro σ hσ
                      rw [Finset.mem_filter] at hσ
                      cases σ with
                      | nil => simp at hσ
                      | cons a l =>
                        simp only [List.head?_cons, Option.some.injEq] at hσ
                        rw [hσ.2]; rfl
                    · intro x hx y hy hxy
                      rw [Finset.coe_filter] at hx hy
                      simp only [Set.mem_setOf_eq] at hx hy
                      cases x with
                      | nil => simp at hx
                      | cons a l =>
                        cases y with
                        | nil => simp at hy
                        | cons b m =>
                          simp only [List.head?_cons, Option.some.injEq] at hx hy
                          simp only [List.tail_cons] at hxy
                          rw [hx.2, hy.2, hxy]
                  rw [e, ← Finset.mul_sum]
                  apply mul_le_of_le_one_right (C.chain.nonneg _ _)
                  apply ih
                  intro τ hτ
                  rw [Finset.mem_image] at hτ
                  obtain ⟨σ, hσ, rfl⟩ := hτ
                  rw [Finset.mem_filter] at hσ
                  have := hs σ hσ.1
                  refine ⟨by rw [List.length_tail]; omega, fun hm => this.2 (List.mem_of_mem_tail hm)⟩
              have h5 : C.chain.P (some i) (some j) +
                  ∑ k : Fin n, (if k = j then 0 else C.chain.P (some i) (some k)) ≤ 1 := by
                have e : ∑ k : Fin n, C.chain.P (some i) (some k) =
                    ∑ k : Fin n, ((if k = j then 0 else C.chain.P (some i) (some k)) +
                      (if k = j then C.chain.P (some i) (some k) else 0)) := by
                  apply Finset.sum_congr rfl; intro k _; split_ifs <;> simp
                rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at e
                simp only [Finset.mem_univ, if_true] at e
                have := hrow i
                have := C.chain.nonneg (some i) none
                linarith
              rw [h1, h3]
              have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h4 k)
              linarith
          have hα : ∀ (U : Finset (Fin n)) (j i : Fin n), j ∈ U →
              ∑' u : {u : List (Fin n) // ∀ x ∈ u, x ∉ U}, pw u.1 j i ≤ 1 := by
            intro U j i hj
            apply tsum_le_of_sum_le' zero_le_one
            intro s
            have e := Finset.sum_map s (Function.Embedding.subtype (fun u : List (Fin n) => ∀ x ∈ u, x ∉ U))
              (fun u => pw u j i)
            simp only [Function.Embedding.coe_subtype] at e
            rw [← e]
            apply hpw_fin j ((s.map (Function.Embedding.subtype _)).sup List.length)
            intro u hu
            refine ⟨Finset.le_sup (f := List.length) hu, ?_⟩
            rw [Finset.mem_map] at hu
            obtain ⟨⟨v, hv⟩, -, rfl⟩ := hu
            intro hjv; exact hv j hjv hj
          have hsummB : ∀ (i : Fin n) (G : List (Fin n) → ℝ) (B : ℝ), (∀ t, |G t| ≤ B) →
              Summable (fun σ => walkTail C.chain i σ * G σ) := by
            intro i G B hB
            apply Summable.of_norm_bounded (g := fun σ => walkTail C.chain i σ * B) ((htail_summ i).mul_right B)
            intro σ
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (htail_nn _ _)]
            exact mul_le_mul_of_nonneg_left (hB _) (htail_nn _ _)
          have hKabs : ∀ T j t, |r j - H T t| ≤ Rs := by
            intro T j t
            have := hHnn T t; have := hHle T t; have := hr j; have := hr_le j
            rw [abs_le]; constructor <;> linarith
          have hΔ : ∀ T j, j ∈ T → ∀ i, ∃ a, 0 ≤ a ∧ a ≤ 1 ∧ (i = j → a = 1) ∧
              val T i - val (T.erase j) i =
                a * ∑' σ, walkTail C.chain j σ * (r j - H (T.erase j) σ) := by
            intro T j hj i
            have e0 : val T i - val (T.erase j) i = ∑' σ, walkTail C.chain i σ *
                (H T (i :: σ) - H (T.erase j) (i :: σ)) := by
              rw [hval]; dsimp only
              rw [← Summable.tsum_sub (hsummB i _ Rs (fun t => hHabs _ _))
                (hsummB i _ Rs (fun t => hHabs _ _))]
              apply tsum_congr; intro σ; ring
            rw [e0]
            simp_rw [hP T j hj]
            by_cases hiT : i ∈ T
            · by_cases hij : i = j
              · subst hij
                refine ⟨1, zero_le_one, le_refl _, fun _ => rfl, ?_⟩
                rw [one_mul]
                apply tsum_congr; intro σ
                simp [List.find?_cons, hiT]
              · refine ⟨0, le_refl _, zero_le_one, fun h => absurd h hij, ?_⟩
                rw [zero_mul]
                refine (tsum_congr (fun σ => ?_)).trans tsum_zero
                have : (i :: σ).find? (fun x => decide (x ∈ T)) = some i := by simp [List.find?_cons, hiT]
                rw [this, if_neg (fun h => hij (Option.some.inj h)), mul_zero]
            · refine ⟨_, tsum_nonneg (fun u => hpw_nn _ _ _), hα T j i hj,
                fun h => absurd (h ▸ hj) hiT, ?_⟩
              rw [← hhit T j i hj (fun σ => r j - H (T.erase j) σ) Rs (fun t => hKabs _ _ _)]
              apply tsum_congr; intro σ
              have h1 : (i :: σ).find? (fun x => decide (x ∈ T)) = σ.find? (fun x => decide (x ∈ T)) := by
                simp [List.find?_cons, hiT]
              have h2 : (i :: σ).dropWhile (fun x => !decide (x ∈ T)) =
                  σ.dropWhile (fun x => !decide (x ∈ T)) := by
                simp [List.dropWhile_cons, hiT]
              rw [h1, h2]
          set m : Fin n → ℝ := fun j => ∑' σ, walkTail C.chain j σ with hm
          have hm_nn : ∀ j, 0 ≤ m j := fun j => tsum_nonneg (fun σ => htail_nn σ j)
          have hgen : ∀ T j, ∑' σ, walkTail C.chain j σ * (r j - H T σ) =
              r j * m j - ∑' σ, walkTail C.chain j σ * H T σ := by
            intro T j
            rw [hm]; dsimp only
            rw [← tsum_mul_left, ← Summable.tsum_sub ((htail_summ j).mul_left (r j))
              (hsummB j _ Rs (fun t => hHabs _ _))]
            apply tsum_congr; intro σ; ring
          have hVin : ∀ j ∈ S, val S j = r j * m j := by
            intro j hj
            rw [hval, hm]; dsimp only
            rw [← tsum_mul_left]
            apply tsum_congr; intro σ; rw [hHmem _ _ _ hj]; ring
          have hVout : ∀ j, j ∉ S → val S j = ∑' σ, walkTail C.chain j σ * H S σ := by
            intro j hj
            rw [hval]; dsimp only
            apply tsum_congr; intro σ; rw [hHnot _ _ _ hj]
          have hgT : ∀ T j, ∑' σ, walkTail C.chain j σ * H T σ =
              ∑ k : Fin n, C.chain.P (some j) (some k) * val T k := by
            intro T j
            rw [hstep j (H T) Rs (fun t => hHabs _ _) (hH0 T)]
          have hL1 : ∀ j, r j * m j ≤ val S j := by
            intro j
            by_cases hj : j ∈ S
            · exact le_of_eq (hVin j hj).symm
            · by_contra hlt
              push_neg at hlt
              have hjT : j ∈ insert j S := Finset.mem_insert_self _ _
              have herase : (insert j S).erase j = S := Finset.erase_insert hj
              choose a ha0 ha1 haj hadiff using hΔ (insert j S) j hjT
              simp_rw [herase, hgen, ← hVout j hj] at hadiff
              have hgain : 0 < r j * m j - val S j := by linarith
              have hsum : ∑ i, (val (insert j S) i - val S i) ≥ val (insert j S) j - val S j :=
                Finset.single_le_sum (f := fun i => val (insert j S) i - val S i)
                  (fun i _ => by rw [hadiff i]; exact mul_nonneg (ha0 i) hgain.le) (Finset.mem_univ j)
              rw [hadiff j, haj j rfl, one_mul] at hsum
              have := hS (insert j S) (Finset.mem_univ _)
              rw [Finset.sum_sub_distrib] at hsum
              linarith
          have hL2 : ∀ j, ∑ k : Fin n, C.chain.P (some j) (some k) * val S k ≤ val S j := by
            intro j
            by_cases hj : j ∈ S
            · choose a ha0 ha1 haj hadiff using hΔ S j hj
              rw [hgen] at hadiff
              set b := ∑' σ, walkTail C.chain j σ * H (S.erase j) σ with hb
              have hgain : 0 ≤ r j * m j - b := by
                by_contra hneg
                push_neg at hneg
                have hsum : ∑ i, (val S i - val (S.erase j) i) ≤ val S j - val (S.erase j) j := by
                  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
                  have := Finset.sum_nonpos (s := Finset.univ.erase j)
                    (f := fun i => val S i - val (S.erase j) i)
                    (fun i _ => by rw [hadiff i]; exact mul_nonpos_of_nonneg_of_nonpos (ha0 i) hneg.le)
                  linarith
                rw [hadiff j, haj j rfl, one_mul] at hsum
                have := hS (S.erase j) (Finset.mem_univ _)
                rw [Finset.sum_sub_distrib] at hsum
                linarith
              have hbk : b = ∑ k : Fin n, C.chain.P (some j) (some k) * val (S.erase j) k := hgT _ j
              have hdiff : ∑ k : Fin n, C.chain.P (some j) (some k) * val S k - b ≤ r j * m j - b := by
                have e : ∑ k : Fin n, C.chain.P (some j) (some k) * val S k - b =
                    ∑ k, (C.chain.P (some j) (some k) * val S k -
                      C.chain.P (some j) (some k) * val (S.erase j) k) := by
                  rw [hbk, Finset.sum_sub_distrib]
                rw [e]
                calc ∑ k, (C.chain.P (some j) (some k) * val S k -
                      C.chain.P (some j) (some k) * val (S.erase j) k)
                    = ∑ k, C.chain.P (some j) (some k) * (a k * (r j * m j - b)) := by
                      apply Finset.sum_congr rfl; intro k _; rw [← mul_sub, hadiff k]
                  _ ≤ ∑ k, C.chain.P (some j) (some k) * (r j * m j - b) := by
                      apply Finset.sum_le_sum; intro k _
                      apply mul_le_mul_of_nonneg_left _ (C.chain.nonneg _ _)
                      calc a k * (r j * m j - b) ≤ 1 * (r j * m j - b) :=
                            mul_le_mul_of_nonneg_right (ha1 k) hgain
                        _ = _ := one_mul _
                  _ = (∑ k, C.chain.P (some j) (some k)) * (r j * m j - b) := by rw [Finset.sum_mul]
                  _ ≤ 1 * (r j * m j - b) := by
                      apply mul_le_mul_of_nonneg_right _ hgain
                      have := hrow j; have := C.chain.nonneg (some j) none; linarith
                  _ = _ := one_mul _
              rw [hVin j hj]; linarith
            · rw [hVout j hj, hgT]
          show ∑' t, w t * R t ≤ ∑' t, w t * H S t
          set Rr : ℕ → Finset (Fin n) → List (Fin n) → ℝ := fun N =>
            Nat.rec (motive := fun _ => Finset (Fin n) → List (Fin n) → ℝ) (fun _ _ => 0)
              (fun _ ih A t => List.casesOn (motive := fun _ => ℝ) t 0
                (fun i σ => r i * (F (insert i A) - F A) + ih (insert i A) σ)) N with hRr
          have hRrnil : ∀ N A, Rr N A [] = 0 := by intro N A; cases N <;> rfl
          have hRrcons : ∀ N A i σ, Rr (N+1) A (i :: σ) =
              r i * (F (insert i A) - F A) + Rr N (insert i A) σ := fun _ _ _ _ => rfl
          have hRs_nn : 0 ≤ Rs := Finset.sum_nonneg (fun i _ => hr i)
          have hRr_bd : ∀ N A t, 0 ≤ Rr N A t ∧ Rr N A t ≤ Rs * (1 - F A) := by
            intro N
            induction N with
            | zero =>
              intro A t
              exact ⟨le_refl _, mul_nonneg hRs_nn (by linarith [hF_le A])⟩
            | succ N ih =>
              intro A t
              cases t with
              | nil =>
                show 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ Rs * (1 - F A)
                exact ⟨le_refl _, mul_nonneg hRs_nn (by linarith [hF_le A])⟩
              | cons i σ =>
                rw [hRrcons]
                have hδ : 0 ≤ F (insert i A) - F A := by
                  linarith [hF_mono A (insert i A) (Finset.subset_insert _ _)]
                obtain ⟨h1, h2⟩ := ih (insert i A) σ
                have h3 : r i * (F (insert i A) - F A) ≤ Rs * (F (insert i A) - F A) :=
                  mul_le_mul_of_nonneg_right (hr_le i) hδ
                have e : Rs * (1 - F A) = Rs * (F (insert i A) - F A) + Rs * (1 - F (insert i A)) := by ring
                exact ⟨add_nonneg (mul_nonneg (hr i) hδ) h1, by linarith⟩
          have hRr_abs : ∀ N A t, |Rr N A t| ≤ Rs := by
            intro N A t
            obtain ⟨h1, h2⟩ := hRr_bd N A t
            rw [abs_of_nonneg h1]
            have := mul_nonneg hRs_nn (hF_nn A)
            nlinarith
          have hRr_eq : ∀ (t : List (Fin n)) (A : Finset (Fin n)) (N : ℕ), t.length ≤ N →
              Rr N A t = ∑ s ∈ Finset.range t.length, (t[s]?.elim 0 r) *
                (F (A ∪ (t.take (s+1)).toFinset) - F (A ∪ (t.take s).toFinset)) := by
            intro t
            induction t with
            | nil => intro A N _; rw [hRrnil]; rfl
            | cons i σ ih =>
              intro A N hN
              obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
              rw [hRrcons, ih (insert i A) N' (by simp at hN; omega), List.length_cons,
                Finset.sum_range_succ']
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.take_succ_cons,
                List.take_zero, List.toFinset_cons, List.toFinset_nil, Finset.union_insert,
                Finset.insert_union, Finset.union_empty, Option.elim]
              exact add_comm _ _
          have hRR : ∀ t N, t.length ≤ N → R t = Rr N ∅ t := by
            intro t N hN
            rw [hRr_eq t ∅ N hN, hR]
            simp only [Finset.empty_union]
          have hval_nn : ∀ i, 0 ≤ val S i := fun i =>
            tsum_nonneg (fun σ => mul_nonneg (htail_nn _ _) (hHnn _ _))
          have hmain : ∀ N A i, ∑' σ, walkTail C.chain i σ * Rr N A (i :: σ) ≤ (1 - F A) * val S i := by
            intro N
            induction N with
            | zero =>
              intro A i
              have : ∑' σ, walkTail C.chain i σ * Rr 0 A (i :: σ) = 0 := by
                refine (tsum_congr (fun σ => ?_)).trans tsum_zero
                show walkTail C.chain i σ * 0 = 0
                exact mul_zero _
              rw [this]
              exact mul_nonneg (by linarith [hF_le A]) (hval_nn i)
            | succ N ih =>
              intro A i
              have hδ : 0 ≤ F (insert i A) - F A := by
                linarith [hF_mono A (insert i A) (Finset.subset_insert _ _)]
              have e1 : ∑' σ, walkTail C.chain i σ * Rr (N+1) A (i :: σ) =
                  r i * (F (insert i A) - F A) * m i +
                    ∑' σ, walkTail C.chain i σ * Rr N (insert i A) σ := by
                simp_rw [hRrcons, mul_add]
                rw [Summable.tsum_add ((htail_summ i).mul_right _) (hsummB i _ Rs (hRr_abs N _))]
                congr 1
                rw [tsum_mul_right]; exact mul_comm _ _
              rw [e1, hstep i (Rr N (insert i A)) Rs (hRr_abs N _) (hRrnil N _)]
              have e2 : ∑ k : Fin n, C.chain.P (some i) (some k) *
                  ∑' σ, walkTail C.chain k σ * Rr N (insert i A) (k :: σ) ≤
                  (1 - F (insert i A)) * val S i := by
                calc _ ≤ ∑ k : Fin n, C.chain.P (some i) (some k) * ((1 - F (insert i A)) * val S k) :=
                      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (ih _ k) (C.chain.nonneg _ _))
                  _ = (1 - F (insert i A)) * ∑ k : Fin n, C.chain.P (some i) (some k) * val S k := by
                      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
                  _ ≤ (1 - F (insert i A)) * val S i :=
                      mul_le_mul_of_nonneg_left (hL2 i) (by linarith [hF_le (insert i A)])
              have e3 : r i * (F (insert i A) - F A) * m i ≤ (F (insert i A) - F A) * val S i := by
                calc r i * (F (insert i A) - F A) * m i = (F (insert i A) - F A) * (r i * m i) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left (hL1 i) hδ
              have e4 : (1 - F A) * val S i =
                  (F (insert i A) - F A) * val S i + (1 - F (insert i A)) * val S i := by ring
              linarith
          have hRHS : ∑' t, w t * H S t = ∑ k : Fin n, C.initial (some k) * val S k :=
            hfirst (H S) Rs (hHabs S) (hH0 S)
          have hX_nn : 0 ≤ ∑ k : Fin n, C.initial (some k) * val S k :=
            Finset.sum_nonneg (fun k _ => mul_nonneg (C.initial_nonneg _) (hval_nn k))
          have hNb : ∀ N, ∑' t, w t * Rr N ∅ t ≤ ∑ k : Fin n, C.initial (some k) * val S k := by
            intro N
            rw [hfirst (Rr N ∅) Rs (hRr_abs N ∅) (hRrnil N ∅)]
            apply Finset.sum_le_sum; intro k _
            apply mul_le_mul_of_nonneg_left _ (C.initial_nonneg _)
            have := hmain N ∅ k
            rwa [hF_empty, sub_zero, one_mul] at this
          rw [hRHS]
          apply tsum_le_of_sum_le' hX_nn
          intro s
          set N := s.sup List.length
          have e5 : ∑ t ∈ s, w t * R t = ∑ t ∈ s, w t * Rr N ∅ t := by
            apply Finset.sum_congr rfl; intro t ht
            rw [hRR t N (Finset.le_sup (f := List.length) ht)]
          rw [e5]
          refine le_trans ?_ (hNb N)
          apply Summable.sum_le_tsum s (fun t _ => mul_nonneg (hw_nn t) (hRr_bd N ∅ t).1)
          apply Summable.of_norm_bounded (g := fun t => w t * Rs) (hw_summ.mul_right Rs)
          intro t
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw_nn t)]
          exact mul_le_mul_of_nonneg_left (hRr_abs _ _ _) (hw_nn t)
