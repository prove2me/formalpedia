-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
-- name    : ProbabilityTheory_chapter_02_ex_2_1_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:56:07.01213+00:00
-- url     : https://prove2.me/theorems/2dfa8d0d-9d43-4ec7-948b-577618796c7b
-- title:
--   Chapter 2, ex_2_1_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `ex_2_1_2`: `diagonalFlip`, `diagonalFlip_ne_row`, `binaryExpansionValue`, `cantorIntervalValue`, `cantorFunction_one_third_false`, and 8 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/ex_2_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open scoped Set
open scoped BigOperators

noncomputable section

def diagonalFlip (F : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun n => !(F n n)

theorem diagonalFlip_ne_row (F : ℕ → ℕ → Bool) (n : ℕ) :
    diagonalFlip F ≠ F n := by
  intro h
  have hcoord := congrArg (fun s : ℕ → Bool => s n) h
  simp [diagonalFlip] at hcoord

def binaryExpansionValue (s : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, if s n then (1 / 2 : ℝ) ^ (n + 1) else 0

def cantorIntervalValue (s : ℕ → Bool) : ℝ :=
  (1 / 2 : ℝ) * Cardinal.cantorFunction (1 / 3 : ℝ) s
theorem cantorFunction_one_third_false :
    Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => false) = 0 := by
  simp [Cardinal.cantorFunction, Cardinal.cantorFunctionAux]
theorem cantorFunction_one_third_true :
    Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => true) = (3 / 2 : ℝ) := by
  rw [Cardinal.cantorFunction]
  have hterm :
      (fun n : ℕ => Cardinal.cantorFunctionAux (1 / 3 : ℝ) (fun _ : ℕ => true) n) =
        fun n : ℕ => (1 / 3 : ℝ) ^ n := by
    ext n
    simp [Cardinal.cantorFunctionAux]
  rw [hterm, tsum_geometric_of_lt_one]
  · norm_num
  · norm_num
  · norm_num
theorem cantorFunction_one_third_nonneg (s : ℕ → Bool) :
    0 ≤ Cardinal.cantorFunction (1 / 3 : ℝ) s := by
  have hle := Cardinal.cantorFunction_le
    (c := (1 / 3 : ℝ)) (f := fun _ : ℕ => false) (g := s)
    (by norm_num) (by norm_num)
    (by intro n h; cases h)
  rw [cantorFunction_one_third_false] at hle
  exact hle
theorem cantorFunction_one_third_le_three_halves (s : ℕ → Bool) :
    Cardinal.cantorFunction (1 / 3 : ℝ) s ≤ (3 / 2 : ℝ) := by
  have hle := Cardinal.cantorFunction_le
    (c := (1 / 3 : ℝ)) (f := s) (g := fun _ : ℕ => true)
    (by norm_num) (by norm_num)
    (by intro n h; trivial)
  rwa [cantorFunction_one_third_true] at hle

def cantorIntervalEmbedding (s : ℕ → Bool) : Set.Icc (0 : ℝ) 1 :=
  ⟨cantorIntervalValue s, by
    constructor
    · have hnonneg := cantorFunction_one_third_nonneg s
      dsimp [cantorIntervalValue]
      nlinarith [hnonneg]
    · have hle := cantorFunction_one_third_le_three_halves s
      dsimp [cantorIntervalValue]
      nlinarith [hle]⟩
theorem cantorIntervalEmbedding_injective :
    Function.Injective cantorIntervalEmbedding := by
  intro s t hst
  have hval := congrArg Subtype.val hst
  have hcf :
      Cardinal.cantorFunction (1 / 3 : ℝ) s =
        Cardinal.cantorFunction (1 / 3 : ℝ) t := by
    dsimp [cantorIntervalEmbedding, cantorIntervalValue] at hval
    nlinarith
  exact Cardinal.cantorFunction_injective (c := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) hcf

theorem sameCardinality_to_nat_countable {α : Type*} {A : Set α}
    (hne : A.Nonempty) (h : SameCardinality A (Set.univ : Set ℕ)) :
    A.Countable := by
  rcases h with ⟨e⟩
  rw [Set.countable_iff_exists_surjective hne]
  refine ⟨fun n => e.symm ⟨n, by trivial⟩, ?_⟩
  intro a
  refine ⟨(e a).1, ?_⟩
  have hn : (⟨(e a).1, by trivial⟩ : (Set.univ : Set ℕ)) = e a := by
    ext
    rfl
  simpa only [hn] using e.symm_apply_apply a

def ex_2_1_2 : Prop :=
  ¬ IsCountableSet (Set.Icc (0 : ℝ) 1)

theorem ex_2_1_2_binary_sequences_uncountable :
    ¬ IsCountableSet (Set.univ : Set (ℕ → Bool)) := by
  rintro ⟨e⟩
  let F : ℕ → ℕ → Bool := fun n => (e.symm ⟨n, by trivial⟩).1
  let sStar : ℕ → Bool := diagonalFlip F
  let nSub : (Set.univ : Set ℕ) := e ⟨sStar, by trivial⟩
  have hrow : F nSub.1 = sStar := by
    have hs : e.symm nSub = ⟨sStar, by trivial⟩ := by
      simp [nSub]
    simpa [F] using congrArg Subtype.val hs
  exact (diagonalFlip_ne_row F nSub.1) hrow.symm


