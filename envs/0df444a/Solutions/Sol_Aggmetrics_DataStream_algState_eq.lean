-- Prove2me | solution 1 for Aggmetrics.DataStream.algState_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:19:04.473196+00:00
-- url     : https://prove2.me/submissions/6694282d-1831-4fe7-829b-bcceaa5e855e

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_succ
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_last

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
open scoped Classical
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n
      = ∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k) := by
  induction n with
  | zero => simp [algState]
  | succ n ih =>
    rw [algState, ih]
    have hk : ∀ k ∈ range n,
        fadeWeight α (n + 1) k • outer (zvec y yt aud arr (n + 1) k) (p k)
          = α • (fadeWeight α n k • outer (zvec y yt aud arr n k) (p k))
            + (if aud k ∧ arr k = n + 1 then
                fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0) := by
      intro k hk'
      have hkn : k < n := Finset.mem_range.mp hk'
      rw [fadeWeight_succ hkn]
      by_cases h : aud k ∧ arr k = n + 1
      · have h1 : zvec y yt aud arr (n + 1) k = y k := by
          unfold zvec
          rw [if_pos ⟨h.1, by omega⟩]
        have h2 : zvec y yt aud arr n k = yt k := by
          unfold zvec
          rw [if_neg (by rintro ⟨_, h3⟩; omega)]
        rw [if_pos h, h1, h2, smul_sub, smul_smul]
        abel
      · have h3 : (aud k ∧ arr k ≤ n + 1) ↔ (aud k ∧ arr k ≤ n) := by
          constructor
          · rintro ⟨h4, h5⟩
            refine ⟨h4, ?_⟩
            have h6 : arr k ≠ n + 1 := fun h7 => h ⟨h4, h7⟩
            omega
          · rintro ⟨h4, h5⟩
            exact ⟨h4, by omega⟩
        have h1 : zvec y yt aud arr (n + 1) k = zvec y yt aud arr n k := by
          unfold zvec
          simp only [h3]
        rw [if_neg h, h1, smul_smul, add_zero]
    have hlast : fadeWeight α (n + 1) n • outer (zvec y yt aud arr (n + 1) n) (p n)
        = (1 - α) • outer (yt n) (p n)
          + (if aud n ∧ arr n = n + 1 then
              fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0) := by
      rw [fadeWeight_last]
      by_cases h : aud n ∧ arr n = n + 1
      · have h1 : zvec y yt aud arr (n + 1) n = y n := by
          unfold zvec
          rw [if_pos ⟨h.1, by omega⟩]
        rw [if_pos h, h1, smul_sub]
        abel
      · have h3 : ¬ (aud n ∧ arr n ≤ n + 1) := by
          rintro ⟨h4, h5⟩
          exact h ⟨h4, by have := harr n; omega⟩
        have h1 : zvec y yt aud arr (n + 1) n = yt n := by
          unfold zvec
          rw [if_neg h3]
        rw [if_neg h, h1, add_zero]
    rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl hk, Finset.sum_add_distrib, ← Finset.smul_sum, hlast]
    abel
end Aggmetrics.DataStream
