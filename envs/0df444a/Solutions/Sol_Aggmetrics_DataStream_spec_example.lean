-- Prove2me | solution 1 for Aggmetrics.DataStream.spec_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:23.361057+00:00
-- url     : https://prove2.me/submissions/c8627df6-8aa0-446e-907c-ca0191d6daa7

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution :
    specFormula ![1 / 2, 1 / 4, 1 / 4]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 7 / 8 ∧
    specFormula ![1 / 2, 1 / 8, 3 / 8]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 13 / 16 := by
  constructor <;>
  · simp only [specFormula, Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_three, Matrix.cons_val_two]
    norm_num
end Aggmetrics.DataStream
