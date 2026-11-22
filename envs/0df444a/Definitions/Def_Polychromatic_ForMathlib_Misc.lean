-- Prove2me | Definitions.Def_Polychromatic_ForMathlib_Misc
-- name    : Polychromatic_ForMathlib_Misc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:34:14.642142+00:00
-- url     : https://prove2.me/theorems/a4812239-8f65-42bc-aff9-7ef84538b583
-- title:
--   Misc
-- statement:
--   Definitions and structural lemmas for Misc, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
set_option autoImplicit true
open Finset
lemma Filter.Tendsto.exists_le_lt {α : Type*} [LinearOrder α] [NoMaxOrder α] {f : ℕ → α}
    (hf : Tendsto f atTop atTop) (n : α) (hn : f 0 ≤ n) : ∃ m, f m ≤ n ∧ n < f (m + 1) := by
  have h : ∃ m, n < f m := (hf.eventually (eventually_gt_atTop n)).exists
  match hm : Nat.find h with
  | 0 => cases hn.not_gt (hm ▸ Nat.find_spec h)
  | m + 1 => have : n < f m.succ := hm ▸ Nat.find_spec h
             refine ⟨m, le_of_not_gt <| Nat.find_min h <| m.lt_succ_self.trans_eq hm.symm, this⟩
lemma StrictMono.exists_le_lt {f : ℕ → ℕ} (hf : StrictMono f) (hf₀ : f 0 = 0) (n : ℕ) :
    ∃ m, f m ≤ n ∧ n < f (m + 1) :=
  hf.tendsto_atTop.exists_le_lt _ (by simp [hf₀])
@[simp] lemma Nat.mod_eq' {a b : ℕ} : a.mod b = a % b := rfl
section
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
end
namespace Finpartition
def equiEndpoint (n k i : ℕ) : ℕ :=
  n / k * i + min (n % k) i
lemma equiEndpoint_lo {n k : ℕ} : equiEndpoint n k 0 = 0 := by simp [equiEndpoint]
lemma equiEndpoint_hi {n k : ℕ} (hk : k ≠ 0) : equiEndpoint n k k = n := by
  rw [equiEndpoint, min_eq_left (Nat.mod_lt n hk.bot_lt).le, Nat.div_add_mod']
lemma equiEndpoint_monotone {n k : ℕ} : Monotone (equiEndpoint n k) := by
  rintro i j h
  rw [equiEndpoint, equiEndpoint]
  gcongr
lemma equiEndpoint_strictMono {n k : ℕ} (hk : k ≠ 0) (hkn : k ≤ n) :
    StrictMono (equiEndpoint n k) := by
  rintro i j h
  rw [equiEndpoint, equiEndpoint]
  apply add_lt_add_of_lt_of_le
  · gcongr
    exact Nat.div_pos hkn hk.bot_lt
  · gcongr
open Function in
theorem equipartitionToIco.extracted_2 {n k a : ℕ} :
    Pairwise
      (Disjoint on (fun i ↦ Ico (a + equiEndpoint n k i) (a + equiEndpoint n k (i + 1)))) := by
  intro i j h
  simp only [Function.onFun, ← Finset.disjoint_coe, coe_Ico]
  wlog hij : i ≤ j generalizing i j
  · exact (this h.symm (by order)).symm
  have : equiEndpoint n k (i + 1) ≤ equiEndpoint n k j :=
    equiEndpoint_monotone (by grind)
  simp [this]
theorem equipartitionToIco.extracted_3 {a b k : ℕ} (hk₀ : k ≠ 0) (hk : k ≤ b - a) :
    ((range k).biUnion
      fun i ↦ Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))) =
      Ico a b := by
  apply subset_antisymm
  · simp only [biUnion_subset_iff_forall_subset, mem_range]
    intro i hi
    apply Ico_subset_Ico (by simp)
    calc
      _ ≤ a + equiEndpoint (b - a) k k := add_le_add_right (equiEndpoint_monotone (by grind)) a
      _ ≤ b := by rw [equiEndpoint_hi hk₀]; omega
  · simp only [subset_iff, mem_Ico, mem_biUnion, mem_range, and_imp]
    intro x hax hxb
    obtain ⟨i, hi, hi'⟩ :=
      (equiEndpoint_strictMono hk₀ hk).exists_le_lt (by rw [equiEndpoint_lo]) (x - a)
    have : i < k := by
      have : equiEndpoint (b - a) k k = b - a := equiEndpoint_hi hk₀
      by_contra!
      have : equiEndpoint (b - a) k k ≤ equiEndpoint (b - a) k i := equiEndpoint_monotone (by grind)
      grind
    exact ⟨i, this, by grind⟩
theorem equipartitionToIco_nonempty {a b k i : ℕ} (hk₀ : k ≠ 0) (hk : k ≤ b - a) :
    (Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))).Nonempty := by
  simp only [nonempty_Ico, add_lt_add_iff_left]
  exact equiEndpoint_strictMono hk₀ hk (Nat.lt_succ_self i)
def equipartitionToIco (a b k : ℕ) : Finpartition (Finset.Ico a b) :=
  if h : k ≠ 0 ∧ k ≤ b - a then {
    parts := (range k).image fun i ↦
      Finset.Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))
    supIndep := by
      rw [supIndep_iff_pairwiseDisjoint]
      simp_rw [coe_image, coe_range]
      apply Set.Pairwise.image
      intro i hi j hj h
      exact equipartitionToIco.extracted_2 h
    sup_parts := by
      rw [sup_eq_biUnion, image_biUnion]
      exact equipartitionToIco.extracted_3 h.1 h.2
    bot_notMem := by
      simp only [bot_eq_empty, mem_image, not_exists, not_and, ← nonempty_iff_ne_empty]
      intro i hi
      exact equipartitionToIco_nonempty h.1 h.2 }
  else ⊥
end Finpartition


