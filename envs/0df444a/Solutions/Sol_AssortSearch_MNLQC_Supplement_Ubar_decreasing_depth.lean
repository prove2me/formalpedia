-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.Ubar_decreasing_depth
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:49.075219+00:00
-- url     : https://prove2.me/submissions/142b6b14-1de1-4de0-b6ea-4c3845a67fc3

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

open AssortSearch
open AssortSearch.MNLQC
open AssortSearch.MNLQC.Supplement

/-- §4.3 (p. 17): in the overlapping assortment model the search threshold `Ū(S)` strictly
decreases as the assortment grows: for `S ⊊ S' ⊊ N` and `b > 0`, `Ū(S') < Ū(S)`. -/
theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (S S' : Finset (Fin n)) (hSS' : S ⊂ S') (hS' : S' ≠ Finset.univ) (b : ℝ) (hb : 0 < b) :
    AssortSearch.FullAssort.Ubar μ v S' b < AssortSearch.FullAssort.Ubar μ v S b := by
      classical
      set γ := Real.eulerMascheroniConstant with hγ
      set V := AssortSearch.FullAssort.outsidePref v S with hVdef
      set W := AssortSearch.FullAssort.outsidePref v S' with hWdef
      have hWpos : 0 < W := by
        have hne : S'ᶜ.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          apply hS'
          simpa using h
        exact Finset.sum_pos (fun i _ => hv i) hne
      have hWV : W < V := by
        obtain ⟨i, hiS', hiS⟩ := Finset.exists_of_ssubset hSS'
        apply Finset.sum_lt_sum_of_subset (Finset.compl_subset_compl.mpr hSS'.subset) (i := i)
        · simpa using hiS
        · simpa using hiS'
        · exact hv i
        · intro j _ _; exact (hv j).le
      have hVpos : 0 < V := lt_trans hWpos hWV
      set D := μ * (Real.log V - Real.log W) with hD
      have hDpos : 0 < D := mul_pos hμ (sub_pos.mpr (Real.log_lt_log hWpos hWV))
      have hlam : ∀ y, AssortSearch.Cannibal.lam μ (y + D) * V
          = AssortSearch.Cannibal.lam μ y * W := by
        intro y
        unfold AssortSearch.Cannibal.lam
        rw [← hγ]
        have : -((y + D) / μ + γ) = -(y / μ + γ) + (Real.log W - Real.log V) := by
          rw [hD]; field_simp; ring
        rw [this, Real.exp_add, Real.exp_sub, Real.exp_log hWpos, Real.exp_log hVpos]
        field_simp
      have hw : ∀ y, AssortSearch.FullAssort.w μ v S' y
          = AssortSearch.FullAssort.w μ v S (y + D) := by
        intro y
        show W / μ * AssortSearch.Cannibal.lam μ y
            * Real.exp (-(AssortSearch.Cannibal.lam μ y * W))
          = V / μ * AssortSearch.Cannibal.lam μ (y + D)
            * Real.exp (-(AssortSearch.Cannibal.lam μ (y + D) * V))
        rw [show V / μ * AssortSearch.Cannibal.lam μ (y + D)
            = AssortSearch.Cannibal.lam μ (y + D) * V / μ by ring, hlam y]
        ring
      have htrans : ∀ (f : ℝ → ℝ) (a c : ℝ),
          ∫ y in Set.Ioi a, f (y + c) = ∫ z in Set.Ioi (a + c), f z := by
        intro f a c
        rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
          ← integral_add_right_eq_self (μ := volume) (fun z => (Set.Ioi (a + c)).indicator f z) c]
        congr 1; ext x
        simp only [Set.indicator, Set.mem_Ioi]
        split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
      have hint_trans : ∀ (f : ℝ → ℝ) (a : ℝ),
          IntegrableOn (fun t => f (t + a)) (Set.Ioi 0) → IntegrableOn f (Set.Ioi a) := by
        intro f a h
        rw [← integrable_indicator_iff measurableSet_Ioi] at h ⊢
        have := h.comp_sub_right a
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Set.indicator, Set.mem_Ioi, sub_add_cancel]
        split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
      set w' := AssortSearch.FullAssort.w μ v S' with hw'def
      have hlampos : ∀ y, 0 < AssortSearch.Cannibal.lam μ y := fun y => Real.exp_pos _
      have hw'eq : ∀ y, w' y = W / μ * AssortSearch.Cannibal.lam μ y
          * Real.exp (-(AssortSearch.Cannibal.lam μ y * W)) := fun y => rfl
      have hwpos : ∀ y, 0 < w' y := by
        intro y; rw [hw'eq]
        have := hlampos y
        positivity
      have hlam_eq : ∀ y, AssortSearch.Cannibal.lam μ y = Real.exp (-γ) * Real.exp (-(1 / μ) * y) := by
        intro y; unfold AssortSearch.Cannibal.lam; rw [← Real.exp_add]; congr 1; field_simp; ring
      have hwle : ∀ y, w' y ≤ W / μ * AssortSearch.Cannibal.lam μ y := by
        intro y; rw [hw'eq]
        have h1 : Real.exp (-(AssortSearch.Cannibal.lam μ y * W)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_pos (hlampos y) hWpos).le)
        have h2 : 0 ≤ W / μ * AssortSearch.Cannibal.lam μ y := by
          have := hlampos y; positivity
        calc _ ≤ W / μ * AssortSearch.Cannibal.lam μ y * 1 := mul_le_mul_of_nonneg_left h1 h2
          _ = _ := mul_one _
      have h0 : IntegrableOn (fun t => t * (W / μ * AssortSearch.Cannibal.lam μ t)) (Set.Ioi 0) := by
        have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1 / μ)
          (by norm_num) one_pos (by positivity)).const_mul (W / μ * Real.exp (-γ))
        refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
        simp only [Real.rpow_one, hlam_eq]; ring
      have hshift_lam : ∀ t u, AssortSearch.Cannibal.lam μ (t + u)
          = Real.exp (-u / μ) * AssortSearch.Cannibal.lam μ t := by
        intro t u; unfold AssortSearch.Cannibal.lam; rw [← Real.exp_add]; congr 1; ring
      have hwcont : Continuous w' := by
        rw [show w' = fun y => W / μ * AssortSearch.Cannibal.lam μ y
          * Real.exp (-(AssortSearch.Cannibal.lam μ y * W)) from funext hw'eq]
        unfold AssortSearch.Cannibal.lam
        fun_prop
      have hbound : ∀ u t, 0 < t → 0 ≤ (t + u - u) * w' (t + u) ∧
          (t + u - u) * w' (t + u) ≤ Real.exp (-u / μ) * (t * (W / μ * AssortSearch.Cannibal.lam μ t)) := by
        intro u t ht
        refine ⟨mul_nonneg (by linarith) (hwpos _).le, ?_⟩
        have := hwle (t + u); rw [hshift_lam] at this
        calc (t + u - u) * w' (t + u) = t * w' (t + u) := by ring
          _ ≤ t * (W / μ * (Real.exp (-u / μ) * AssortSearch.Cannibal.lam μ t)) :=
              mul_le_mul_of_nonneg_left this ht.le
          _ = _ := by ring
      have hint : ∀ u, IntegrableOn (fun y => (y - u) * w' y) (Set.Ioi u) := by
        intro u; apply hint_trans
        refine Integrable.mono' (h0.const_mul (Real.exp (-u / μ))) ?_ ?_
        · exact (by fun_prop : Continuous fun t => (t + u - u) * w' (t + u)).aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hb := hbound u t ht
          rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact hb.2
      set M := ∫ t in Set.Ioi 0, t * (W / μ * AssortSearch.Cannibal.lam μ t) with hMdef
      have hupper : ∀ u, AssortSearch.FullAssort.searchGain μ v S' u ≤ Real.exp (-u / μ) * M := by
        intro u
        unfold AssortSearch.FullAssort.searchGain
        have := htrans (fun y => (y - u) * w' y) 0 u
        rw [zero_add] at this
        rw [← this, hMdef, ← integral_const_mul]
        apply integral_mono_of_nonneg
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact (hbound u t ht).1
        · exact h0.const_mul _
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact (hbound u t ht).2
      have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi (fun t ht => by
        have := hlampos t
        have ht' : (0:ℝ) < t := ht
        exact mul_nonneg ht'.le (by positivity))
      have hne : ∃ u, AssortSearch.FullAssort.searchGain μ v S' u ≤ b := by
        refine ⟨μ * Real.log ((M + 1) / b), (hupper _).trans ?_⟩
        rw [show -(μ * Real.log ((M + 1) / b)) / μ = -Real.log ((M + 1) / b) by field_simp,
          Real.exp_neg, Real.exp_log (by positivity)]
        rw [inv_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      set m := W / μ * Real.exp (-(1 / μ + γ)) * Real.exp (-(Real.exp (-γ) * W)) with hmdef
      have hmpos : 0 < m := by positivity
      have hwlow : ∀ y ∈ Set.Ioc (0:ℝ) 1, m ≤ w' y := by
        intro y hy
        rw [hw'eq]
        have l1 : Real.exp (-(1 / μ + γ)) ≤ AssortSearch.Cannibal.lam μ y := by
          unfold AssortSearch.Cannibal.lam
          apply Real.exp_le_exp.mpr
          have : y / μ ≤ 1 / μ := div_le_div_of_nonneg_right hy.2 hμ.le
          linarith
        have l2 : AssortSearch.Cannibal.lam μ y ≤ Real.exp (-γ) := by
          unfold AssortSearch.Cannibal.lam
          apply Real.exp_le_exp.mpr
          have : 0 ≤ y / μ := div_nonneg hy.1.le hμ.le
          linarith
        have l3 : Real.exp (-(Real.exp (-γ) * W)) ≤ Real.exp (-(AssortSearch.Cannibal.lam μ y * W)) := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_right l2 hWpos.le
          linarith
        have p1 : 0 < W / μ := by positivity
        have := mul_le_mul_of_nonneg_left l1 p1.le
        calc m = W / μ * Real.exp (-(1 / μ + γ)) * Real.exp (-(Real.exp (-γ) * W)) := rfl
          _ ≤ W / μ * AssortSearch.Cannibal.lam μ y * Real.exp (-(AssortSearch.Cannibal.lam μ y * W)) :=
              mul_le_mul this l3 (Real.exp_pos _).le (by have := hlampos y; positivity)
      have hlower : ∀ u ≤ 0, -u * m ≤ AssortSearch.FullAssort.searchGain μ v S' u := by
        intro u hu
        unfold AssortSearch.FullAssort.searchGain
        calc -u * m = ∫ y in Set.Ioc (0:ℝ) 1, -u * m := by simp
          _ ≤ ∫ y in Set.Ioc (0:ℝ) 1, (y - u) * w' y := by
              apply setIntegral_mono_on (integrableOn_const (by simp))
                ((hint u).mono_set (fun y hy => by
                  simp only [Set.mem_Ioc, Set.mem_Ioi] at hy ⊢; linarith [hy.1]))
                measurableSet_Ioc
              intro y hy
              exact mul_le_mul (by linarith [hy.1]) (hwlow y hy) hmpos.le (by linarith [hy.1])
          _ ≤ ∫ y in Set.Ioi u, (y - u) * w' y := by
              apply setIntegral_mono_set (hint u)
              · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
                exact mul_nonneg (by simp only [Set.mem_Ioi] at hy; linarith) (hwpos y).le
              · exact (show Set.Ioc (0:ℝ) 1 ⊆ Set.Ioi u from fun y hy => by
                  simp only [Set.mem_Ioc, Set.mem_Ioi] at hy ⊢; linarith [hy.1]).eventuallyLE
      have hbdd : BddBelow {u | AssortSearch.FullAssort.searchGain μ v S' u ≤ b} := by
        refine ⟨-(b / m), fun u hu => ?_⟩
        by_contra h
        push Not at h
        have hbm : 0 < b / m := div_pos hb hmpos
        have hu0 : u ≤ 0 := by linarith
        have h1 := hlower u hu0
        have h2 : b < -u * m := (div_lt_iff₀ hmpos).mp (by linarith)
        have h3 : AssortSearch.FullAssort.searchGain μ v S' u ≤ b := hu
        linarith
      have hΦ : ∀ u, AssortSearch.FullAssort.searchGain μ v S' u
          = AssortSearch.FullAssort.searchGain μ v S (u + D) := by
        intro u
        unfold AssortSearch.FullAssort.searchGain
        rw [← htrans (fun z => (z - (u + D)) * AssortSearch.FullAssort.w μ v S z)]
        congr 1; ext y
        rw [show AssortSearch.FullAssort.w μ v S' y = AssortSearch.FullAssort.w μ v S (y + D) from hw y]
        ring_nf
      unfold AssortSearch.FullAssort.Ubar
      obtain ⟨u0, hu0⟩ := hne
      have hAne : {u | AssortSearch.FullAssort.searchGain μ v S u ≤ b}.Nonempty :=
        ⟨u0 + D, by show AssortSearch.FullAssort.searchGain μ v S (u0 + D) ≤ b; rw [← hΦ]; exact hu0⟩
      have key : sInf {u | AssortSearch.FullAssort.searchGain μ v S' u ≤ b} + D
          ≤ sInf {u | AssortSearch.FullAssort.searchGain μ v S u ≤ b} := by
        apply le_csInf hAne
        intro a ha
        have : sInf {u | AssortSearch.FullAssort.searchGain μ v S' u ≤ b} ≤ a - D :=
          csInf_le hbdd (show AssortSearch.FullAssort.searchGain μ v S' (a - D) ≤ b by
            rw [hΦ, sub_add_cancel]; exact ha)
        linarith
      linarith
