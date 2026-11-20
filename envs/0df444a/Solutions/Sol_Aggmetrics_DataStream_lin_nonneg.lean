-- Prove2me | solution 1 for Aggmetrics.DataStream.lin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:59:18.189111+00:00
-- url     : https://prove2.me/submissions/76fae223-20cf-43b6-a1f6-628c6cc1986b

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {a : Fin 4 → ℝ} (ha : ∀ i, 0 ≤ a i) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : ∀ r s, 0 ≤ T r s) : 0 ≤ lin a T := by
  unfold lin
  have := ha 0; have := ha 1; have := ha 2; have := ha 3
  have := hT 0 0; have := hT 0 1; have := hT 1 0; have := hT 1 1
  positivity
end Aggmetrics.DataStream
