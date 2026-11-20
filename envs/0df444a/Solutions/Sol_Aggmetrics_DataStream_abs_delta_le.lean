-- Prove2me | solution 1 for Aggmetrics.DataStream.abs_delta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:18.34231+00:00
-- url     : https://prove2.me/submissions/eede2434-0000-4330-a783-17633567c1ae

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction

set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (y yt p : ℕ → Fin m → ℝ)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (k : ℕ) (a b : Fin m) :
    |(y k a - yt k a) * p k b| ≤ 1 := by
  have h1 := hy k a
  have h2 := hyt k a
  have h3 := hp k b
  have hd : |y k a - yt k a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hpp : |p k b| ≤ 1 := abs_le.mpr ⟨by linarith [h3.1], h3.2⟩
  calc |(y k a - yt k a) * p k b| = |y k a - yt k a| * |p k b| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hd hpp (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1
end Aggmetrics.DataStream
