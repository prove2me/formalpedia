-- Prove2me | solution 1 for Arxiv2610_39302.subsample_interval_scaling
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:38:49.1519+00:00
-- url     : https://prove2.me/submissions/eb6b5c69-a5aa-413c-b478-3272e7d93e67

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology Matrix Finset

namespace S71SI
open Arxiv2610_39302

lemma cnt (N k : ℕ) (T : Finset (Fin N)) (hk : T.card ≤ k) :
    ((univ.powersetCard k).filter (fun S => T ⊆ S)).card = (N - T.card).choose (k - T.card) := by
  have hc : (univ \ T).card = N - T.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  rw [← hc, ← card_powersetCard]
  apply card_nbij' (fun S => S \ T) (fun S => S ∪ T)
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard_univ, mem_powersetCard] at hS ⊢
    refine ⟨sdiff_subset_sdiff (subset_univ _) le_rfl, ?_⟩
    rw [card_sdiff_of_subset hS.2, hS.1.2]
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard_univ, mem_powersetCard] at hS ⊢
    refine ⟨⟨subset_univ _, ?_⟩, subset_union_right⟩
    have hd : Disjoint S T := by
      rw [disjoint_left]; intro a ha haT
      have := hS.1 ha; simp [haT] at this
    rw [card_union_of_disjoint hd, hS.2]; omega
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard_univ, mem_powersetCard] at hS
    simp [sdiff_union_of_subset hS.2]
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard_univ, mem_powersetCard] at hS
    have hd : Disjoint S T := by
      rw [disjoint_left]; intro a ha haT
      have := hS.1 ha; simp [haT] at this
    exact union_sdiff_cancel_right hd

lemma sumsq (N n : ℕ) (hn : 2 ≤ n) (y : Fin N → ℝ) :
    ∑ S ∈ (univ : Finset (Fin N)).powersetCard n, (∑ i ∈ S, y i) ^ 2 =
      ∑ i, ∑ j, y i * y j *
        (if i = j then ((N - 1).choose (n - 1) : ℝ) else ((N - 2).choose (n - 2) : ℝ)) := by
  have h1 : ∀ S : Finset (Fin N), (∑ i ∈ S, y i) ^ 2 =
      ∑ i, ∑ j, y i * y j * (if i ∈ S ∧ j ∈ S then (1:ℝ) else 0) := by
    intro S
    rw [sq, sum_mul_sum]
    have : ∀ i, ∑ j, y i * y j * (if i ∈ S ∧ j ∈ S then (1:ℝ) else 0) =
        if i ∈ S then ∑ j ∈ S, y i * y j else 0 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, true_and, if_true, mul_ite, mul_one, mul_zero]
        rw [← sum_filter]; congr 1; ext; simp
      · simp [hi]
    simp_rw [this]
    rw [sum_ite_mem, univ_inter]
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, sum_boole]
  congr 1
  have hT : ∀ S : Finset (Fin N), (i ∈ S ∧ j ∈ S) ↔ ({i, j} : Finset (Fin N)) ⊆ S := by
    intro S; simp [insert_subset_iff]
  simp_rw [hT]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have := cnt N n {i} (by simp; omega)
    simp only [insert_eq_of_mem (mem_singleton_self i)]
    rw [this]; simp
  · rw [if_neg hij]
    have hc : ({i, j} : Finset (Fin N)).card = 2 := card_pair hij
    have := cnt N n {i, j} (by rw [hc]; omega)
    rw [this, hc]

end S71SI

open Arxiv2610_39302 S71SI in
theorem solution (x : Fin 1024 → ℝ) :
    subsampleSpread x 800 = Real.sqrt (224 / 800) * (Real.sqrt (sampleVar x) / Real.sqrt 1024) := by
  set m := popMean x
  set y : Fin 1024 → ℝ := fun i => x i - m
  have hy0 : ∑ i, y i = 0 := by
    simp only [y, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, m,
      popMean]
    push_cast; field_simp; ring
  have hsub : ∀ S ∈ (univ : Finset (Fin 1024)).powersetCard 800,
      (subMean x S - m) ^ 2 = (∑ i ∈ S, y i) ^ 2 / 800 ^ 2 := by
    intro S hS
    rw [mem_powersetCard_univ] at hS
    simp only [subMean, hS, y, sum_sub_distrib, sum_const, nsmul_eq_mul]
    push_cast; field_simp
  have hss := sumsq 1024 800 (by norm_num) y
  have hQ : ∑ i, ∑ j, y i * y j *
      (if i = j then ((1024 - 1).choose (800 - 1) : ℝ) else ((1024 - 2).choose (800 - 2) : ℝ)) =
      (((1024 - 1).choose (800 - 1) : ℝ) - ((1024 - 2).choose (800 - 2) : ℝ)) * ∑ i, y i ^ 2 := by
    have : ∀ i j, y i * y j *
        (if i = j then ((1024 - 1).choose (800 - 1) : ℝ) else ((1024 - 2).choose (800 - 2) : ℝ)) =
        ((1024 - 2).choose (800 - 2) : ℝ) * (y i * y j) +
        (if i = j then (((1024 - 1).choose (800 - 1) : ℝ) - ((1024 - 2).choose (800 - 2) : ℝ)) *
          y i ^ 2 else 0) := by
      intro i j; split_ifs with h
      · subst h; ring
      · ring
    simp_rw [this, sum_add_distrib, sum_ite_eq, mem_univ, if_true, ← mul_sum, ← sum_mul, hy0]
    ring
  unfold subsampleSpread
  rw [sum_congr rfl hsub, ← sum_div, hss, hQ]
  have hv : sampleVar x = (∑ i, y i ^ 2) / 1023 := by
    simp only [sampleVar, y, m]; norm_num
  rw [hv, ← Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 1024), ← Real.sqrt_mul (by norm_num)]
  clear hss hQ hsub
  rw [show (1024 - 1 : ℕ) = 1023 from rfl, show (800 - 1 : ℕ) = 799 from rfl,
    show (1024 - 2 : ℕ) = 1022 from rfl, show (800 - 2 : ℕ) = 798 from rfl]
  have e1 := Nat.add_one_mul_choose_eq 1023 799
  have e2 := Nat.add_one_mul_choose_eq 1022 798
  have e3 := Nat.choose_succ_right_eq 1022 798
  have e4 := Nat.choose_succ_succ' 1022 798
  rw [show (1023 + 1 : ℕ) = 1024 from rfl, show (799 + 1 : ℕ) = 800 from rfl] at e1
  rw [show (1022 + 1 : ℕ) = 1023 from rfl, show (798 + 1 : ℕ) = 799 from rfl] at e2
  rw [show (798 + 1 : ℕ) = 799 from rfl] at e3
  rw [show (1022 + 1 : ℕ) = 1023 from rfl, show (798 + 1 : ℕ) = 799 from rfl] at e4
  have hc0 : 0 < Nat.choose 1022 798 := Nat.choose_pos (by norm_num)
  rw [show (1022 - 798 : ℕ) = 224 from rfl] at e3
  clear e2
  generalize Nat.choose 1022 798 = c at *
  generalize Nat.choose 1022 799 = d at *
  generalize Nat.choose 1023 799 = e at *
  generalize Nat.choose 1024 800 = C at *
  have r1 : (1024:ℝ) * e = C * 800 := by exact_mod_cast e1
  have r3 : (d:ℝ) * 799 = c * 224 := by exact_mod_cast e3
  have r4 : (e:ℝ) = c + d := by exact_mod_cast e4
  have hc : (0:ℝ) < c := by exact_mod_cast hc0
  have hd : (d:ℝ) = c * 224 / 799 := by field_simp; linarith
  have hC : (C:ℝ) = 1024 * (c + c * 224 / 799) / 800 := by rw [← hd, ← r4]; linarith
  rw [r4, hd, hC]
  apply congrArg Real.sqrt
  field_simp
  ring
