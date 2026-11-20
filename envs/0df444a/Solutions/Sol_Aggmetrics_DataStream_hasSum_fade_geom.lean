-- Prove2me | solution 1 for Aggmetrics.DataStream.hasSum_fade_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:29:36.991084+00:00
-- url     : https://prove2.me/submissions/ffda06fd-cbef-4577-9272-44c0c1b8f057

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_fade_tail_sum


set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    HasSum (fun i : ℕ => (1 - α) * α ^ (i + t)) (α ^ t) := by
  have : (fun i : ℕ => (1 - α) * α ^ (i + t)) = fun j => (1 - α) * α ^ (t + j) := by
    funext i
    rw [Nat.add_comm]
  rw [this]
  exact fade_tail_sum h0 h1 t
end Aggmetrics.DataStream
