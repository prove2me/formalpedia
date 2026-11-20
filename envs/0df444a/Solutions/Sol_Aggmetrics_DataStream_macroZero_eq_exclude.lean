-- Prove2me | solution 1 for Aggmetrics.DataStream.macroZero_eq_exclude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:22.854947+00:00
-- url     : https://prove2.me/submissions/e4808237-ee99-4a35-8a05-e9a79611c4fb

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (e : ℝ)
    (hne : active u ≠ 0) (hm : (m : ℝ) ≠ 0) (he : macroExclude u v = some e) :
    macroZero u v = some (e * (active u : ℝ) / (m : ℝ)) := by
  unfold macroExclude at he
  rw [if_neg hne] at he
  have hact : (active u : ℝ) ≠ 0 := by exact_mod_cast hne
  have he' : (∑ j, if u j = true then v j else 0) / (active u : ℝ) = e := Option.some.inj he
  unfold macroZero
  congr 1
  rw [← he']
  field_simp
end Aggmetrics.DataStream
