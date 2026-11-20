-- Prove2me | solution 1 for Aggmetrics.DataStream.algStateE_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:27:36.423201+00:00
-- url     : https://prove2.me/submissions/85a95121-a3c9-4d96-b13c-821f89c2aba3

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_algState_sub_algStateE
import Theorems.Thm_Aggmetrics_DataStream_algState_eq


set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algStateE α ε y yt p aud arr n
      = (∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k))
        - lostState α ε y yt p aud arr n := by
  rw [← algState_eq α y yt p aud arr harr n, ← algState_sub_algStateE α ε y yt p aud arr harr n]
  abel
end Aggmetrics.DataStream
