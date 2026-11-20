-- Prove2me | solution 1 for Aggmetrics.DataStream.defect_min_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:56.815481+00:00
-- url     : https://prove2.me/submissions/af3d51d0-1e21-4d7e-8b47-d72f27446858

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution : defect (fun x y => min x y) softEx softEx = 3 / 2 := by
  norm_num [defect, softEx, Fin.sum_univ_three, Matrix.cons_val_two, min_def, abs_of_nonneg, abs_of_nonpos]
end Aggmetrics.DataStream
