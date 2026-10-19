-- Prove2me | solution 1 for AgriSubsidy.Combined.prop2_proof_affine
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:06:35.655312+00:00
-- url     : https://prove2.me/submissions/e84d5baa-16d6-453b-89ea-723b6b499b84

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Majorization
set_option autoImplicit false
namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma sum_le_top {N : ℕ} (u : Fin N→ℝ) (S : Finset (Fin N)) :
    (∑i∈S,u i) ≤ topSum u S.card := by
  have hk : S.card≤N := by simpa using Finset.card_le_card (Finset.subset_univ S)
  unfold topSum; rw [dif_pos hk]
  exact Finset.le_sup' (fun T : Finset (Fin N) => ∑i∈T,u i) (by simp)
lemma top_le {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) (r : ℝ)
    (h : ∀S : Finset (Fin N),S.card=k→(∑i∈S,u i)≤r) : topSum u k≤r := by
  unfold topSum; rw [dif_pos hk]
  apply Finset.sup'_le
  intro S hS
  exact h S (Finset.mem_powersetCard.mp hS).2
lemma top_attained {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) :
    ∃ S : Finset (Fin N),S.card=k ∧ topSum u k=∑i∈S,u i := by
  unfold topSum; rw [dif_pos hk]
  obtain ⟨S,hS,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.powersetCard_nonempty.mpr (show k≤(Finset.univ : Finset (Fin N)).card by simpa))
    (fun S : Finset (Fin N) => ∑i∈S,u i)
  exact ⟨S,(Finset.mem_powersetCard.mp hS).2,he⟩
lemma top_affine {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) (c d : ℝ) (hc : 0≤c) :
    topSum (fun i=>c*u i+d) k=c*topSum u k+(k:ℝ)*d := by
  apply le_antisymm
  · apply top_le _ hk
    intro S hS
    have hs := sum_le_top u S
    rw [hS] at hs
    have hh := mul_le_mul_of_nonneg_left hs hc
    simpa [Finset.sum_add_distrib,←Finset.mul_sum, hS] using add_le_add_right hh ((k:ℝ)*d)
  · obtain ⟨S,hS,he⟩ := top_attained u hk
    have hs := sum_le_top (fun i=>c*u i+d) S
    simpa [Finset.sum_add_distrib,←Finset.mul_sum,hS,←he] using hs
lemma top_neg {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) :
    topSum (fun i=>-u i) k=topSum u (N-k)-∑i,u i := by
  classical
  apply le_antisymm
  · apply top_le _ hk
    intro S hS
    have hs := sum_le_top u Sᶜ
    have hc : Sᶜ.card=N-k := by simp [Finset.card_compl,hS]
    rw [hc] at hs
    have he := Finset.sum_add_sum_compl S u
    simp only [Finset.sum_neg_distrib]
    linarith
  · obtain ⟨S,hS,he⟩ := top_attained u (show N-k≤N by omega)
    have hc : Sᶜ.card=k := by simp [Finset.card_compl,hS,Nat.sub_sub_self hk]
    have hs := sum_le_top (fun i=>-u i) Sᶜ
    rw [hc] at hs
    have hsum := Finset.sum_add_sum_compl S u
    simp only [Finset.sum_neg_distrib] at hs
    rw [he]
    linarith
lemma majorizes_neg {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v) :
    Majorizes (fun i=>-u i) (fun i=>-v i) := by
  constructor
  · intro k hk
    rw [top_neg v hk,top_neg u hk,h.2]
    exact sub_le_sub_right (h.1 (N-k) (by omega)) _
  · simp [Finset.sum_neg_distrib,h.2]
lemma majorizes_affine_nonneg {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v)
    (c d : ℝ) (hc : 0≤c) : Majorizes (fun i=>c*u i+d) (fun i=>c*v i+d) := by
  constructor
  · intro k hk
    rw [top_affine v hk c d hc,top_affine u hk c d hc]
    exact add_le_add (mul_le_mul_of_nonneg_left (h.1 k hk) hc) le_rfl
  · simp [Finset.sum_add_distrib,←Finset.mul_sum,h.2]
lemma majorizes_affine {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v) (c d : ℝ) :
    Majorizes (fun i=>c*u i+d) (fun i=>c*v i+d) := by
  by_cases hc : 0≤c
  · exact majorizes_affine_nonneg u v h c d hc
  · have hh := majorizes_affine_nonneg (fun i=>-u i) (fun i=>-v i)
      (majorizes_neg u v h) (-c) d (by linarith)
    simpa using hh
end AgriResearch

open AgriSubsidy.Combined

theorem solution {N : ℕ} (u v : Fin N → ℝ)
    (h : Majorizes u v) (c d : ℝ) :
    Majorizes (fun j => c * u j + d) (fun j => c * v j + d) := by exact AgriResearch.majorizes_affine u v h c d


#print axioms solution
