-- Prove2me | solution 1 for Aggmetrics.DataStream.evicted_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:27:34.978127+00:00
-- url     : https://prove2.me/submissions/bc8ef6a5-ba08-4021-a7c4-4658bfa58cc8

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_evicted_change_bound


set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (n s : ℕ) (D : Finset ℕ)
    (hD : ∀ k ∈ D, k < n ∧ s ≤ n - 1 - k) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1) :
    |∑ k ∈ D, fadeWeight α n k * d k| ≤ α ^ s := by
  have h := evicted_change_bound h0 h1 s (D.image (fun k => n - 1 - k))
    (by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      exact (hD k hk).2)
    (fun j => d (n - 1 - j)) (fun j => hd _)
  rw [Finset.sum_image (by
    intro k hk k' hk' hkk
    have := hD k hk
    have := hD k' hk'
    simp only at hkk
    omega)] at h
  have heq : ∑ k ∈ D, fadeWeight α n k * d k
      = ∑ k ∈ D, (1 - α) * α ^ (n - 1 - k) * d (n - 1 - (n - 1 - k)) :=
    Finset.sum_congr rfl (fun k hk => by
      have := (hD k hk).1
      have e : n - 1 - (n - 1 - k) = k := by omega
      rw [e]
      rfl)
  rw [heq]
  exact h
end Aggmetrics.DataStream
