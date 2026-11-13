-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F001
-- name    : ProbabilityTheory_chapter_02_thm_2_9_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T18:38:35.864564+00:00
-- url     : https://prove2.me/theorems/da9fd586-28eb-466f-b377-981fcdc5de96
-- title:
--   Chapter 2, thm_2_9: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_9`: `q_bij`, `q_seq`, `VitaliSet`, `VitaliSeq`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_9.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

noncomputable section Vitali_set

namespace Vitali_set

open Classical   
open Rat
open Set

instance : Infinite Q_I_Type := by
  classical
  refine Infinite.of_injective
    (fun n : ℕ =>
      ⟨(1 : ℚ) / (n + 2),
        by
          constructor
          · -- 0 ≤ 1 / (n + 2)
            have h : (0 : ℚ) < n + 2 := by
              -- n + 2 ≥ 2 > 0
              have : (0 : ℚ) < (2 : ℕ) := by norm_num
              have : (0 : ℚ) < (n : ℚ) + 2 := by
                have hn : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
                linarith
              exact this
            have h' := div_nonneg (show (0 : ℚ) ≤ 1 by norm_num) (le_of_lt h)
            simpa using h'
          · -- 1 / (n + 2) < 1
            have hpos : (0 : ℚ) < n + 2 := by
              have : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
              linarith
            have hlt : (1 : ℚ) < n + 2 := by
              -- n + 2 ≥ 2 > 1
              have : (2 : ℚ) ≤ n + 2 := by
                have : (2 : ℕ) ≤ n + 2 := by exact Nat.le_add_left 2 n
                exact_mod_cast this
              linarith
            -- use the → direction of `div_lt_one`
            have h' : (1 : ℚ) / (n + 2) < 1 :=
              (div_lt_one hpos).2 hlt
            simpa using h'⟩)

    (by -- Injectivity proof
      intro n m h
      have := congrArg Subtype.val h
      have h' : (1 : ℚ) / (n + 2) = 1 / (m + 2) := this
      have hn : (n : ℚ) + 2 ≠ 0 := by linarith
      have hm : (m : ℚ) + 2 ≠ 0 := by linarith
      have := (div_eq_div_iff hn hm).1 h'
      have h'' : (m : ℚ) = n := by
        have := congrArg (fun x => x - (2 : ℚ)) this
        simpa using this
      norm_cast at h''
      exact h''.symm)

instance : Denumerable Q_I_Type :=
  Denumerable.ofEncodableOfInfinite Q_I_Type

def q_bij : ℕ ≃ Q_I_Type :=
  (Denumerable.eqv Q_I_Type).symm

noncomputable def q_seq (n : ℕ) : ℝ := (q_bij n).val

noncomputable def VitaliSet : Set ℝ :=
  range (fun (x : Quotient vitaliSetoid) => (@Quotient.out _ vitaliSetoid x).val)

noncomputable def VitaliSeq (n : ℕ) : Set ℝ := translate VitaliSet (q_seq n)

end Vitali_set


