-- Prove2me | solution 1 for AhlswedeKhachatrian.four_n
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T22:27:33.893648+00:00
-- url     : https://prove2.me/submissions/f7e6e0db-fe6b-431c-a330-7f9dba21001f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AhlswedeKhachatrian
import Theorems.Thm_AhlswedeKhachatrian_interval_bound_unique

namespace AhlswedeKhachatrian

open Finset

section Aux

private lemma card_inter_add {α : Type*} [DecidableEq α] [Fintype α] (x s : Finset α) :
    #(x ∩ s) + #(x ∩ sᶜ) = #x := by
  rw [← Finset.card_union_of_disjoint]
  · rw [← inter_union_distrib_left]; simp
  · exact Finset.disjoint_left.2 fun a h1 h2 => (Finset.mem_compl.1 (Finset.mem_inter.1 h2).2) (Finset.mem_inter.1 h1).2

variable (m : ℕ)

/-- The first `2 (m+1)` points of `Fin (4 (m+1))`. -/
private def P : Finset (Fin (4 * (m + 1))) := univ.filter (fun i => i.1 < 2 * (m + 1))

private lemma card_P : #(P m) = 2 * (m + 1) := by
  have : P m = (Finset.range (2 * (m + 1))).attachFin (fun i hi => by
      simp at hi; omega) := by
    ext i; simp [P, Finset.mem_attachFin]
  rw [this, Finset.card_attachFin, card_range]

private lemma card_Pc : #((P m)ᶜ) = 2 * (m + 1) := by
  rw [card_compl, card_P]; simp [Fintype.card_fin]; omega

private lemma f_compl (x : Finset (Fin (4 * (m + 1)))) (hx : #x = 2 * (m + 1)) :
    #(xᶜ ∩ P m) = 2 * (m + 1) - #(x ∩ P m) := by
  have h1 : #(x ∩ P m) + #(xᶜ ∩ P m) = #(P m) := by
    have := card_inter_add (P m) x
    rw [inter_comm (P m) x, inter_comm (P m) xᶜ] at this
    exact this
  rw [card_P] at h1
  omega

private def U : Finset (Finset (Fin (4 * (m + 1)))) := powersetCard (2 * (m + 1)) univ

private lemma card_U : #(U m) = (4 * (m + 1)).choose (2 * (m + 1)) := by
  simp [U, card_powersetCard]

private lemma mem_U (x : Finset (Fin (4 * (m + 1)))) : x ∈ U m ↔ #x = 2 * (m + 1) := by
  simp [U, mem_powersetCard]

private lemma frankl_eq :
    frankl (4 * (m + 1)) (2 * (m + 1)) 2 m = (U m).filter (fun x => m + 2 ≤ #(x ∩ P m)) := by
  ext x
  have key : (x.filter (fun i => i.1 < 2 + 2 * m)) = x ∩ P m := by
    ext i; simp [P, Finset.mem_inter]; intro _; omega
  simp only [frankl, Finset.mem_filter, Finset.mem_univ, true_and, mem_U, key]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

private lemma split_inter (y1 y2 : Finset (Fin (4 * (m + 1)))) (h1 : y1 ⊆ P m)
    (h2 : y2 ⊆ (P m)ᶜ) :
    (y1 ∪ y2) ∩ P m = y1 ∧ (y1 ∪ y2) ∩ (P m)ᶜ = y2 := by
  constructor <;> ext a <;>
  · have ha1 := @h1 a
    have ha2 := @h2 a
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl] at *
    tauto

private lemma card_eq_mid :
    #((U m).filter (fun x => #(x ∩ P m) = m + 1)) = ((2 * (m + 1)).choose (m + 1)) ^ 2 := by
  have : #((U m).filter (fun x => #(x ∩ P m) = m + 1)) =
      #(powersetCard (m + 1) (P m) ×ˢ powersetCard (m + 1) (P m)ᶜ) := by
    refine Finset.card_nbij' (fun x => (x ∩ P m, x ∩ (P m)ᶜ)) (fun y => y.1 ∪ y.2) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, mem_U] at hx
      have := card_inter_add x (P m)
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard,
        Finset.inter_subset_right, true_and]
      exact ⟨hx.2, by omega⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hy
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      obtain ⟨e1, e2⟩ := split_inter m y.1 y.2 h1 h3
      have hd : Disjoint y.1 y.2 :=
        Finset.disjoint_of_subset_left h1 (Finset.disjoint_of_subset_right h3 disjoint_compl_right)
      rw [Finset.mem_coe, Finset.mem_filter, mem_U, e1]
      rw [Finset.card_union_of_disjoint hd]
      exact ⟨by omega, h2⟩
    · intro x hx
      simp only
      rw [← Finset.inter_union_distrib_left]; simp
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hy
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      obtain ⟨e1, e2⟩ := split_inter m y.1 y.2 h1 h3
      simp only [e1, e2]
  rw [this, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    card_P, card_Pc]
  ring

private lemma two_card_frankl :
    2 * #(frankl (4 * (m + 1)) (2 * (m + 1)) 2 m) + ((2 * (m + 1)).choose (m + 1)) ^ 2
      = (4 * (m + 1)).choose (2 * (m + 1)) := by
  rw [frankl_eq, ← card_eq_mid, ← card_U]
  set T := (U m).filter (fun x => m + 2 ≤ #(x ∩ P m)) with hT
  set M := (U m).filter (fun x => #(x ∩ P m) = m + 1) with hM
  set L := (U m).filter (fun x => #(x ∩ P m) < m + 1) with hL
  have hUeq : U m = (T ∪ M) ∪ L := by
    ext x
    simp only [hT, hM, hL, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      have : #(x ∩ P m) < m + 1 ∨ #(x ∩ P m) = m + 1 ∨ m + 2 ≤ #(x ∩ P m) := by omega
      rcases this with h1 | h1 | h1
      · exact Or.inr ⟨h, h1⟩
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inl (Or.inl ⟨h, h1⟩)
    · intro h; rcases h with (h | h) | h <;> exact h.1
  have hd1 : Disjoint T M := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [hT, hM, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint (T ∪ M) L := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [hT, hM, hL, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hcard : #(U m) = #T + #M + #L := by
    conv_lhs => rw [hUeq]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hTL : #L = #T := by
    refine Finset.card_nbij' (fun x => xᶜ) (fun x => xᶜ) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [hL, Finset.mem_coe, Finset.mem_filter, mem_U] at hx
      have := f_compl m x hx.1
      simp only [hT, Finset.mem_coe, Finset.mem_filter, mem_U, Finset.card_compl,
        Fintype.card_fin]
      refine ⟨by omega, by omega⟩
    · intro x hx
      simp only [hT, Finset.mem_coe, Finset.mem_filter, mem_U] at hx
      have hc : #xᶜ = 2 * (m + 1) := by
        simp only [Finset.card_compl, Fintype.card_fin]; omega
      have := f_compl m x hx.1
      simp only [hL, Finset.mem_coe, Finset.mem_filter, mem_U]
      refine ⟨hc, by omega⟩
    · intro x _; simp
    · intro x _; simp
  omega

private lemma interval_mem (m : ℕ) :
    ((4 * (m + 1) : ℕ) : ℚ) ∈ interval (2 * (m + 1)) 2 m := by
  have hm : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp only [interval, if_true, Set.mem_Ioi, threshold]
    push_cast; norm_num
  · have hm0 : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hpos
    have hne : m ≠ 0 := by omega
    simp only [interval, hne, if_false, Set.mem_Ioo, threshold]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    have hj : (0 : ℚ) < (j : ℚ) + 1 := by positivity
    have hj2 : (0 : ℚ) < (j : ℚ) + 1 + 1 := by positivity
    constructor
    · rw [← sub_pos]
      have : (4 * ((j : ℚ) + 1 + 1)) - (2 * ((j : ℚ) + 1 + 1) - 2 + 1) * (2 + (2 - 1) / ((j : ℚ) + 1 + 1))
          = 1 / ((j : ℚ) + 1 + 1) := by field_simp; ring
      linarith [this, show (0:ℚ) < 1 / ((j : ℚ) + 1 + 1) by positivity]
    · rw [← sub_pos]
      have : (2 * ((j : ℚ) + 1 + 1) - 2 + 1) * (2 + (2 - 1) / ((j : ℚ) + 1)) - (4 * ((j : ℚ) + 1 + 1))
          = 1 / ((j : ℚ) + 1) := by field_simp; ring
      linarith [this, show (0:ℚ) < 1 / ((j : ℚ) + 1) by positivity]

end Aux

end AhlswedeKhachatrian

open AhlswedeKhachatrian Finset

theorem solution {n : ℕ} {A : AhlswedeKhachatrian.Family (4 * n)} (hA : A.Sized (2 * n) ∧ A.Inter 2) :
    2 * #A ≤ (4 * n).choose (2 * n) - (2 * n).choose n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
      have h1 := hA.1 x hx
      have h2 := hA.2 x hx x hx
      rw [Finset.inter_self, h1] at h2
      omega
    simp [this]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := AhlswedeKhachatrian.interval_bound_unique (n := 4 * (m + 1)) (k := 2 * (m + 1)) (t := 2) (r := m)
      (A := A) ⟨by norm_num, by omega, by omega, by omega⟩ (AhlswedeKhachatrian.interval_mem m) hA
    have := AhlswedeKhachatrian.two_card_frankl m
    have := h.1
    omega
