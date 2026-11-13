-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_9_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:56:58.451825+00:00
-- url     : https://prove2.me/theorems/b2d69567-ee03-4704-921b-959bdb626019
-- title:
--   Chapter 2, thm_2_9: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_9`: `I`, `translate`, `IsVitaliMeasure`, `vitali_rel`, `vitali_rel_equiv`, and 2 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_9.lean

import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

noncomputable section Vitali_set

namespace Vitali_set

open Classical   
open Rat
open Set

def I : Set ℝ := Icc 0 1

def translate (A : Set ℝ) (d : ℝ) : Set ℝ :=
  (fun x => Int.fract (x + d)) '' A

def IsVitaliMeasure (m : Set ℝ → ENNReal) : Prop :=

  (∀ A, ¬(A ⊆ I) → m A = 0) ∧
  (m ∅ = 0) ∧

  (∀ A B, A ⊆ I → B ⊆ I → A ⊆ B → m A ≤ m B) ∧

  (∀ f : ℕ → Set ℝ,
    (∀ n, f n ⊆ I) →               
    Pairwise (fun i j => Disjoint (f i) (f j)) →     
    m (⋃ n, f n) = ∑' n, m (f n)) ∧

  (∀ A, A ⊆ I → ∀ d : ℝ, m (translate A d) = m A) ∧

  (∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    m (Icc a b) = ENNReal.ofReal (b - a))

def vitali_rel (x y : ℝ) : Prop := ∃ q : ℚ, x - y = q

lemma vitali_rel_equiv : Equivalence vitali_rel := by
  constructor
  ·  
    intro x; use 0; simp
  ·  
    intro x y ⟨q, h⟩
    use -q

    rw [Rat.cast_neg]

    rw [← h]

    ring

  ·  
    intro x y z ⟨q1, h1⟩ ⟨q2, h2⟩
    use q1 + q2

    rw [Rat.cast_add]

    rw [← h1, ← h2]

    ring

instance vitaliSetoid : Setoid I :=
  { r := fun x y => vitali_rel x.1 y.1
    iseqv := by
      constructor
      · intro x
        apply vitali_rel_equiv.1
      ·  
        intro x y h
        exact vitali_rel_equiv.symm h
      ·  
        intro x y z h1 h2
        exact vitali_rel_equiv.trans h1 h2
  }

def Q_I_Type := {x : ℚ // 0 ≤ x ∧ x < 1}

instance : Encodable Q_I_Type :=
  (inferInstance : Encodable {x : ℚ // 0 ≤ x ∧ x < 1})

end Vitali_set


