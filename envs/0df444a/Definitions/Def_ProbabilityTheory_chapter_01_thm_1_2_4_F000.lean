-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_2_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:28:21.237208+00:00
-- url     : https://prove2.me/theorems/2722b51a-ead3-4d28-938f-b933ca78131a
-- title:
--   Chapter 1, thm_1_2_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2_4`: `lowerSumSet`, `lowerDarboux`, `concatPartition`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

def lowerSumSet (a c : ℝ) (f α : ℝ → ℝ) : Set ℝ :=
  { y | ∃ P : Partition a c, y = lowerSum P f α }

noncomputable def lowerDarboux (a c : ℝ) (f α : ℝ → ℝ) : ℝ :=
  sSup (lowerSumSet a c f α)

def concatPartition {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) : Partition a b where
  n := P1.n + P2.n
  hn := by
    have h1 := P1.hn
    have h2 := P2.hn
    omega
  pts := fun i =>

    if h : i.val ≤ P1.n then
      P1.pts ⟨i.val, by omega⟩

    else
      P2.pts ⟨i.val - P1.n, by have := i.isLt; omega⟩

  pts_start := by

    exact P1.pts_start

  pts_end := by

    have h_nle : ¬ ((Fin.last (P1.n + P2.n)).val ≤ P1.n) := by
      have h1 := P2.hn
      grind
    rw [dif_neg h_nle]

    have eq_last : (⟨(Fin.last (P1.n + P2.n)).val - P1.n, by omega⟩ : Fin (P2.n + 1)) = Fin.last P2.n := by
      ext
      change (P1.n + P2.n) - P1.n = P2.n
      omega
    rw [eq_last]
    exact P2.pts_end

  strict_mono := by
    intro i j hij
    have h_val_lt : i.val < j.val := hij

    change (if hi : i.val ≤ P1.n then _ else _) < (if hj : j.val ≤ P1.n then _ else _)
    split_ifs with hi hj
    ·  
      apply P1.strict_mono
      exact h_val_lt
    ·  
      have h_left : P1.pts ⟨i.val, by omega⟩ ≤ P1.pts ⟨P1.n, by omega⟩ := by
        apply P1.strict_mono.monotone
        exact hi
      have eq1 : (⟨P1.n, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; change P1.n = P1.n; omega
      have eq2 : (⟨0, by omega⟩ : Fin (P2.n + 1)) = 0 := by ext; change 0 = 0; omega
      have h_mid1 : P1.pts ⟨P1.n, by omega⟩ = c := by rw [eq1, P1.pts_end]
      have h_mid2 : c = P2.pts ⟨0, by omega⟩ := by rw [eq2, P2.pts_start]

      have h_right : P2.pts ⟨0, by omega⟩ < P2.pts ⟨j.val - P1.n, by omega⟩ := by
        apply P2.strict_mono
        change 0 < j.val - P1.n
        omega

      have h_left_c : P1.pts ⟨i.val, by omega⟩ ≤ c := le_trans h_left (le_of_eq h_mid1)
      have h_c_right : c < P2.pts ⟨j.val - P1.n, by omega⟩ := lt_of_eq_of_lt h_mid2 h_right

      exact lt_of_le_of_lt h_left_c h_c_right
    ·  
        exfalso
        omega
    ·  
        apply P2.strict_mono
        change i.val - P1.n < j.val - P1.n
        omega

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4


