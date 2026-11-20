-- Prove2me | solution 1 for Aggmetrics.DataStream.RunningExample.precision_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:17.422416+00:00
-- url     : https://prove2.me/submissions/50c50b26-239f-4236-a6bc-38056f79ca8c

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
import Theorems.Thm_Aggmetrics_DataStream_RunningExample_window_tables

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample
namespace Aggmetrics.DataStream.RunningExample
theorem _root_.solution :
    measure aPrec bPrec (∑ j, classTable (winState 4 y p 8) j) = 3 / 4 ∧
    (omega bPrec (winState 4 y p 8) 0 = 1 / 4 ∧ omega bPrec (winState 4 y p 8) 1 = 1 / 2 ∧
      omega bPrec (winState 4 y p 8) 2 = 1 / 4) ∧
    (measure aPrec bPrec (classTable (winState 4 y p 8) 0) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 1) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 2) = 0) ∧
    (∑ j, omega bPrec (winState 4 y p 8) j * measure aPrec bPrec (classTable (winState 4 y p 8) j)
      = 3 / 4) ∧
    ((measure aPrec bPrec (classTable (winState 4 y p 8) 0)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 1)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 2)) / 3 = 2 / 3) := by
  obtain ⟨h0, h1, h2⟩ := window_tables
  have hsum : ∑ j, classTable (winState 4 y p 8) j = !![3 / 4, 1 / 4; 1 / 4, 7 / 4] := by
    rw [Fin.sum_univ_three, h0, h1, h2]
    ext r s
    fin_cases r <;> fin_cases s <;> simp <;> norm_num
  have hden : ∀ j, lin bPrec (classTable (winState 4 y p 8) j) = ![1 / 4, 1 / 2, 1 / 4] j := by
    intro j
    fin_cases j
    · simp [lin, bPrec, h0]
    · simp [lin, bPrec, h1] <;> norm_num
    · simp [lin, bPrec, h2]
  have hom : ∀ j, omega bPrec (winState 4 y p 8) j = ![1 / 4, 1 / 2, 1 / 4] j := by
    intro j
    unfold omega
    rw [Fin.sum_univ_three]
    simp only [hden]
    fin_cases j <;> simp <;> norm_num
  have hm0 : measure aPrec bPrec (classTable (winState 4 y p 8) 0) = 1 := by
    simp [measure, lin, aPrec, bPrec, h0]
  have hm1 : measure aPrec bPrec (classTable (winState 4 y p 8) 1) = 1 := by
    simp [measure, lin, aPrec, bPrec, h1]
  have hm2 : measure aPrec bPrec (classTable (winState 4 y p 8) 2) = 0 := by
    simp [measure, lin, aPrec, bPrec, h2]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨hm0, hm1, hm2⟩, ?_, ?_⟩
  · rw [hsum]
    simp [measure, lin, aPrec, bPrec]
    norm_num
  · rw [hom]; simp
  · rw [hom]; simp
  · rw [hom]; simp
  · rw [Fin.sum_univ_three, hm0, hm1, hm2, hom, hom, hom]
    simp
    norm_num
  · rw [hm0, hm1, hm2]
    norm_num
end Aggmetrics.DataStream.RunningExample
