-- Prove2me | solution 1 for Aggmetrics.DataStream.weighted_ratio_mixture_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:58:55.973661+00:00
-- url     : https://prove2.me/submissions/20251ac1-fff0-4198-a0a5-21df7472e624

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (num den : Fin m → ℝ)
    (hnum : ∀ j, den j = 0 → num j = 0) (hpos : 0 < ∑ j, den j) :
    (∑ j, num j) / (∑ j, den j)
      = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : den j = 0
  · simp [hj, hnum j hj]
  · field_simp [hj, hpos.ne']
end Aggmetrics.DataStream
