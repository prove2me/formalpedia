-- Prove2me | solution 1 for Aggmetrics.DataStream.defect_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:56.413734+00:00
-- url     : https://prove2.me/submissions/288d8769-cfac-4b52-8717-eb0aed85d11d

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (yt p : Fin m → ℝ) (hy : ∑ a, yt a = 1) (hp : ∑ b, p b = 1) :
    defect (fun x y => x * y) yt p = 0 := by
  unfold defect
  have h1 : ∀ b, ∑ a, yt a * p b = p b := fun b => by rw [← Finset.sum_mul, hy, one_mul]
  have h2 : ∀ a, ∑ b, yt a * p b = yt a := fun a => by rw [← Finset.mul_sum, hp, mul_one]
  simp [h1, h2]
end Aggmetrics.DataStream
