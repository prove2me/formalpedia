-- Prove2me | solution 1 for Aggmetrics.DataStream.sum_ne_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:56.539619+00:00
-- url     : https://prove2.me/submissions/5b4df8fe-2f7a-4884-9c92-9942c8298cd7

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (f : Fin m → ℝ) (j : Fin m) :
    ∑ x, (if x = j then (0 : ℝ) else 1) * f x = ∑ x ∈ univ.erase j, f x := by
  have h1 : ∑ x ∈ univ.erase j, (if x = j then (0 : ℝ) else 1) * f x
      = ∑ x, (if x = j then (0 : ℝ) else 1) * f x :=
    Finset.sum_subset (Finset.erase_subset j univ) (fun x _ hx => by
      have : x = j := by simpa using hx
      simp [this])
  rw [← h1]
  exact Finset.sum_congr rfl (fun x hx => by simp [Finset.ne_of_mem_erase hx])
end Aggmetrics.DataStream
