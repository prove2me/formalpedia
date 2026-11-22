-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
-- name    : LeanPool_NashWilliams_Combinatorics_Front_Rank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:04.954829+00:00
-- url     : https://prove2.me/theorems/c9409a1e-b6b3-4071-b165-3cfc4e4dd1a4
-- title:
--   Rank
-- statement:
--   Definitions and structural lemmas for Rank, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Theorems.Thm_Front_IsInit_eq_of_length
public import Theorems.Thm_Front_IsInit_getElem
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_Front_range_prefix_range
attribute [local simp] Front.isInit_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set List Ordinal
universe u
noncomputable section
namespace Front
def tree (F : Set (List ℕ)) : Set (List ℕ) :=
  {s | ∃ t ∈ F, s <+: t}
def treeExt (F : Set (List ℕ)) (a b : List ℕ) : Prop :=
  a ∈ tree F ∧ b ∈ tree F ∧ b <+: a ∧ b ≠ a
theorem strictMono_of_pairwise_map {b : ℕ → ℕ}
    (h : ∀ n, ((List.range n).map b).Pairwise (· < ·)) : StrictMono b := by
  intro i j hij
  have hlen : ((List.range (j + 1)).map b).length = j + 1 := by simp
  have hp := (List.pairwise_iff_getElem.mp (h (j + 1))) i j (by omega) (by omega) hij
  simpa using hp
theorem exists_strictMono_comp {M b : ℕ → ℕ} (hM : StrictMono M) (hb : StrictMono b)
    (hsub : ∀ i, b i ∈ Set.range M) : ∃ g : ℕ → ℕ, StrictMono g ∧ M ∘ g = b := by
  choose g hg using hsub
  refine ⟨g, ?_, funext hg⟩
  intro i j hij
  have : M (g i) < M (g j) := by rw [hg, hg]; exact hb hij
  exact hM.lt_iff_lt.mp this
theorem IsFront.wellFounded_treeExt {F : Set (List ℕ)} {M : ℕ → ℕ} (hF : IsFront F M) :
    WellFounded (treeExt F) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  -- `hf n : treeExt F (f (n+1)) (f n)`, i.e. `f 0 ⊏ f 1 ⊏ ⋯` is an ascending tower.
  have hmem : ∀ n, f n ∈ tree F := fun n => (hf n).2.1
  have hpre : ∀ n, f n <+: f (n + 1) := fun n => (hf n).2.2.1
  have hne : ∀ n, f n ≠ f (n + 1) := fun n => (hf n).2.2.2
  -- The lengths strictly increase, so `n ≤ |f n|`.
  have hlt : ∀ n, (f n).length < (f (n + 1)).length := by
    intro n
    rcases lt_or_eq_of_le (hpre n).length_le with h | h
    · exact h
    · exact absurd ((hpre n).eq_of_length h) (hne n)
  have hlen_ge : ∀ n, n ≤ (f n).length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hlt k; omega
  -- The tower is nested.
  have hnest : ∀ {n m : ℕ}, n ≤ m → f n <+: f m := by
    intro n m h
    induction h with
    | refl => exact List.prefix_rfl
    | step _ ih => exact ih.trans (hpre _)
  -- Each node is strictly increasing (a sublist of an element of `F`).
  have hsorted : ∀ n, (f n).Pairwise (· < ·) := by
    intro n
    obtain ⟨u, hu, hpu⟩ := hmem n
    exact List.Pairwise.sublist hpu.sublist (hF.sorted u hu)
  -- The limit `b` of the tower.
  have hlen1 : ∀ i, i < (f (i + 1)).length := fun i =>
    lt_of_lt_of_le (Nat.lt_succ_self i) (hlen_ge (i + 1))
  set b : ℕ → ℕ := fun i => (f (i + 1))[i]'(hlen1 i) with hb_def
  -- `b` agrees with every node long enough to reach the index.
  have hagree : ∀ {i m : ℕ}, i + 1 ≤ m → (h : i < (f m).length) → (f m)[i] = b i := by
    intro i m hm _
    exact ((hnest hm).getElem (hlen1 i)).symm
  -- Every initial segment of `b` is a prefix of a sufficiently long node.
  have hb_pre : ∀ {n m : ℕ}, n ≤ m → (List.range n).map b <+: f m := by
    intro n m hnm
    have hnlen : n ≤ (f m).length := le_trans hnm (hlen_ge m)
    have heq : (List.range n).map b = (f m).take n := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left hnlen]
      · intro i h1 _
        have hi : i < n := by simpa using h1
        rw [List.getElem_take, getElem_map, getElem_range]
        exact (hagree (by omega) (lt_of_lt_of_le hi hnlen)).symm
    rw [heq]
    exact List.take_prefix n (f m)
  -- `b` is strictly increasing with entries in `M`.
  have hbmono : StrictMono b := strictMono_of_pairwise_map fun n =>
    List.Pairwise.sublist (hb_pre (le_refl n)).sublist (hsorted n)
  have hbmem : ∀ i, b i ∈ Set.range M := by
    intro i
    obtain ⟨u, hu, hpu⟩ := hmem (i + 1)
    exact hF.subM u hu (b i) (hpu.subset (List.getElem_mem (hlen1 i)))
  -- Apply Density: some `t ∈ F` is an initial segment of `b`.
  obtain ⟨g, hg, hgb⟩ := exists_strictMono_comp hF.mono hbmono hbmem
  obtain ⟨t, ht, hInit⟩ := hF.dense g hg
  rw [hgb] at hInit
  -- Extend `t` by one entry of `b`; it lands inside some `u ∈ F`.
  obtain ⟨u, hu, hpu⟩ := hmem (t.length + 1)
  have htpre : t <+: (List.range (t.length + 1)).map b := by
    conv_lhs => rw [hInit]
    exact (range_prefix_range (Nat.le_succ _)).map b
  have hbu : (List.range (t.length + 1)).map b <+: f (t.length + 1) := hb_pre (le_refl _)
  have hEq : t = u := hF.incomp t ht u hu ((htpre.trans hbu).trans hpu)
  -- But then `u = t` is a prefix of the strictly longer `f (|t|+1)`.
  have h1 : t.length + 1 ≤ (f (t.length + 1)).length := hlen_ge _
  have h2 : (f (t.length + 1)).length ≤ u.length := hpu.length_le
  have h3 : u.length = t.length := by rw [hEq]
  omega
def IsFront.rank {F : Set (List ℕ)} {M : ℕ → ℕ} (hF : IsFront F M) : Ordinal :=
  letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  IsWellFounded.rank (treeExt F) []
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
end Front


