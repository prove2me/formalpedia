-- Prove2me | solution 1 for Aggmetrics.DataStream.macroExclude_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:22.354809+00:00
-- url     : https://prove2.me/submissions/556c3099-5034-4a1c-9608-1b91139b6a3d

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (u : Fin m → Bool) (v v' : Fin m → ℝ)
    (h : ∀ j, u j = true → v j = v' j) : macroExclude u v = macroExclude u v' := by
  unfold macroExclude
  congr 3
  exact Finset.sum_congr rfl (fun j _ => by by_cases hj : u j = true <;> simp [hj, h j])
end Aggmetrics.DataStream
