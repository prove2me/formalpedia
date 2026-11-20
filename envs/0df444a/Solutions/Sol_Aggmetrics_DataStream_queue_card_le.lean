-- Prove2me | solution 1 for Aggmetrics.DataStream.queue_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:19.746078+00:00
-- url     : https://prove2.me/submissions/33e52c90-2213-4830-9059-79a3055948f3

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction

set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {N : ℕ}
    (hN : (1 - α) * α ^ N < ε) (n : ℕ) (P : ℕ → Prop) :
    ((range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k)).card ≤ N := by
  have hinj : Set.InjOn (fun k => n - 1 - k)
      ↑((range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k)) := by
    intro k hk k' hk' h
    have h1 := (Finset.mem_filter.mp hk).1
    have h2 := (Finset.mem_filter.mp hk').1
    simp only [Finset.mem_range] at h1 h2
    simp only at h
    omega
  have hmaps : ∀ k ∈ (range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k),
      (fun k => n - 1 - k) k ∈ range N := by
    intro k hk
    obtain ⟨hkr, hP, hε⟩ := Finset.mem_filter.mp hk
    rw [Finset.mem_range]
    by_contra hlt
    push_neg at hlt
    have : fadeWeight α n k ≤ (1 - α) * α ^ N := by
      unfold fadeWeight
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1.le hlt) (by linarith)
    linarith
  calc _ ≤ (range N).card :=
        Finset.card_le_card_of_injOn _
          (by first
            | exact fun k hk => hmaps k hk
            | exact fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk))) hinj
    _ = N := Finset.card_range N
end Aggmetrics.DataStream
