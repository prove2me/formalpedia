-- Prove2me | solution 1 for Aggmetrics.DataStream.algState_sub_algStateE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:17.334099+00:00
-- url     : https://prove2.me/submissions/5265c9a7-67a7-4df4-a1d3-b04eb323e3ff

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_succ


set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n - algStateE α ε y yt p aud arr n
      = lostState α ε y yt p aud arr n := by
  induction n with
  | zero => simp [algState, algStateE, lostState]
  | succ n ih =>
    rw [algState, algStateE]
    have hS : (∑ k ∈ (range (n + 1)).filter (fun k => aud k ∧ arr k = n + 1),
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)))
        - (∑ k ∈ (range (n + 1)).filter
            (fun k => aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)),
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)))
        = ∑ k ∈ range n, if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0 := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_range_succ]
      have hlast : ((if aud n ∧ arr n = n + 1 then
            fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0)
          - (if aud n ∧ arr n = n + 1 ∧ (n = n ∨ ε ≤ fadeWeight α n n) then
            fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0)) = 0 := by
        by_cases h : aud n ∧ arr n = n + 1
        · simp [h]
        · simp [h]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := by
        have := Finset.mem_range.mp hk
        omega
      by_cases h1 : aud k ∧ arr k = n + 1
      · by_cases h2 : ε ≤ fadeWeight α n k
        · have h2' : ¬ fadeWeight α n k < ε := not_lt.mpr h2
          simp [h1, h2, h2', hkn]
        · have h2' : fadeWeight α n k < ε := not_le.mp h2
          simp [h1, h2, h2', hkn]
      · have a1 : ¬ (aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)) :=
          fun h => h1 ⟨h.1, h.2.1⟩
        have a2 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) :=
          fun h => h1 ⟨h.1, h.2.1⟩
        rw [if_neg h1, if_neg a1, if_neg a2]
        simp
    have hstep : ∀ k ∈ range n,
        (if discarded α ε aud arr (n + 1) k then
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0)
        = α • (if discarded α ε aud arr n k then
            fadeWeight α n k • (outer (y k) (p k) - outer (yt k) (p k)) else 0)
          + (if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0) := by
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hak := harr k
      rw [fadeWeight_succ hkn]
      by_cases hc1 : arr k ≤ n
      · have e1 : discarded α ε aud arr (n + 1) k ↔ discarded α ε aud arr n k := by
          unfold discarded
          constructor
          · rintro ⟨a, b, c, d⟩
            exact ⟨a, hc1, c, d⟩
          · rintro ⟨a, b, c, d⟩
            exact ⟨a, by omega, c, d⟩
        have e2 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
          rintro ⟨_, h, _⟩
          omega
        by_cases hd : discarded α ε aud arr n k
        · rw [if_pos (e1.mpr hd), if_pos hd, if_neg e2, add_zero, smul_smul]
        · rw [if_neg (fun h => hd (e1.mp h)), if_neg hd, if_neg e2]
          simp
      · by_cases hc2 : arr k = n + 1
        · have e1 : ¬ discarded α ε aud arr n k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e2 : discarded α ε aud arr (n + 1) k
              ↔ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
            unfold discarded
            constructor
            · rintro ⟨a, b, c, d⟩
              refine ⟨a, hc2, ?_⟩
              rw [hc2] at d
              simpa using d
            · rintro ⟨a, b, d⟩
              refine ⟨a, by omega, by omega, ?_⟩
              rw [b]
              simpa using d
          rw [if_neg e1]
          simp only [smul_zero, zero_add]
          by_cases hh : (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε)
          · rw [if_pos (e2.mpr hh), if_pos hh]
          · rw [if_neg (fun h => hh (e2.mp h)), if_neg hh]
        · have e1 : ¬ discarded α ε aud arr n k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e2 : ¬ discarded α ε aud arr (n + 1) k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e3 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
            rintro ⟨_, h, _⟩
            omega
          rw [if_neg e1, if_neg e2, if_neg e3]
          simp
    have hlost : lostState α ε y yt p aud arr (n + 1)
        = α • lostState α ε y yt p aud arr n
          + ∑ k ∈ range n, if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
              fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0 := by
      unfold lostState
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
        ← Finset.smul_sum]
      have hlastn : (if discarded α ε aud arr (n + 1) n then
          fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0) = 0 := by
        rw [if_neg]
        unfold discarded
        rintro ⟨_, h, h', _⟩
        have := harr n
        omega
      rw [hlastn, add_zero]
    have hA : algState α y yt p aud arr n
        = algStateE α ε y yt p aud arr n + lostState α ε y yt p aud arr n := by
      rw [← ih]
      abel
    rw [hlost, hA, ← hS]
    simp only [smul_add]
    abel
end Aggmetrics.DataStream
