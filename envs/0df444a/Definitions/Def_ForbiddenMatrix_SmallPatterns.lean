-- Prove2me | Definitions.Def_ForbiddenMatrix_SmallPatterns
-- name    : ForbiddenMatrix_SmallPatterns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:09:35.039723+00:00
-- url     : https://prove2.me/theorems/2d1a69e4-7fb9-4cb7-b042-d240d08bab6a
-- title:
--   Small Patterns
-- statement:
--   Definitions and structural lemmas for Small Patterns, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean

module
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_ForbiddenMatrix_MatrixOperations
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Equiv.Fin.Basic
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_by_rows_ub
public import Theorems.Thm_density_le_ex_of_not_contains
public import Theorems.Thm_ex_zero
public import Theorems.Thm_split_density
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix
attribute [local simp] contains_of_isEmpty
attribute [local simp] ex_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Set
variable {α β : Type*} [LinearOrder α] [LinearOrder β]
def IdentityPattern (n : ℕ) (i j : Fin n) : Prop := i = j
@[nolint unusedArguments]
def AllPattern (m n : ℕ) : Fin m → Fin n → Prop := fun _ _ ↦ True
abbrev VerticalPattern (m : ℕ) : Fin m → Fin 1 → Prop := AllPattern m 1
abbrev HorizontalPattern (n : ℕ) : Fin 1 → Fin n → Prop := AllPattern 1 n
abbrev TrivialPattern : Fin 1 → Fin 1 → Prop := AllPattern 1 1
@[simp] lemma identityPattern_one : IdentityPattern 1 = TrivialPattern := by
  ext i j; simp [IdentityPattern, AllPattern, Subsingleton.elim i j]
def HatPattern : Fin 2 → Fin 3 → Prop :=
  ![
    ![False, True, False],
    ![True, False, True]
   ]
@[simp] lemma ex_of_isEmpty [IsEmpty α] [IsEmpty β] (P : α → β → Prop) (n : ℕ) : ex P n = 0 := by
  simp [ex]
@[simp] lemma ex_trivialPattern (n : ℕ) : ex TrivialPattern n = 0 := by
  simp only [ex, Finset.sup_eq_zero, mem_filter, Finset.mem_univ, true_and, density, card_eq_zero,
    not_imp_comm (a := Contains _ _), ← Finset.nonempty_iff_ne_empty, Finset.Nonempty, Prod.exists,
    forall_exists_index]
  exact fun M i j hij ↦ ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [hij]⟩
example (n : ℕ) : ex (HorizontalPattern 2) n ≤ n := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M noH2P
  let Pred_min_Ofrow := fun i j ↦ ∀ j', M i j' → j ≤ j'
  let M1 (i j : Fin n) : Prop := M i j ∧ Pred_min_Ofrow i j
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ Pred_min_Ofrow i j
  have dm1 : density M1 ≤ n := by
    have h_row_one i : row_density M1 i ≤ 1 := by
      by_contra H
      simp only [row_density, not_le, one_lt_card_iff, mem_filter, Finset.mem_univ, true_and, ne_eq,
        exists_and_left] at H
      obtain ⟨a, ha, b, hb, aneqb⟩ := H
      simp only [M1, Pred_min_Ofrow] at ha hb
      have : a = b := by
        refine Fin.le_antisymm ?h1 ?h2
        · -- a ≤ b
          apply ha.2
          exact hb.1
        · -- b ≤ a
          apply hb.2
          exact ha.1
      contradiction
    simpa using density_by_rows_ub M1 h_row_one
  have M2_avoids_trivial : ¬ Contains TrivialPattern M2 := by
    rintro ⟨f, hf, g, hg, prop⟩
    --  M2    g(0)
    -- f(0)    1
    simp only [TrivialPattern, AllPattern, not_forall, not_le, forall_const, Fin.forall_fin_one,
      Fin.isValue, M2, Pred_min_Ofrow] at prop
    obtain ⟨hfa, a, ha, ha2⟩ := prop
    --  M  a g(0)
    -- f(0) 1 1
    have : Contains (HorizontalPattern 2) M :=
      ⟨f, hf, ![a, g 0], by simpa [StrictMono, Fin.forall_fin_two], by
        simp [AllPattern, Fin.forall_fin_one, Fin.forall_fin_two, *]⟩
    contradiction
  have dm2 := calc
        density M2
    _ ≤ ex TrivialPattern n := density_le_ex_of_not_contains M2 M2_avoids_trivial
    _ = 0 := ex_trivialPattern n
  calc
        density M
    _ = density M1 + density M2 := split_density M Pred_min_Ofrow
    _ ≤ n + density M2 := by simp only [dm1, add_le_add_iff_right]
    _ ≤ n + 0 := by simp only [dm2, add_le_add_iff_left]
    _ ≤ n := by omega


