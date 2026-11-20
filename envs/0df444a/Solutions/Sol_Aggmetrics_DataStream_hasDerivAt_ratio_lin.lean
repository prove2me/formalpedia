-- Prove2me | solution 1 for Aggmetrics.DataStream.hasDerivAt_ratio_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:29:56.874917+00:00
-- url     : https://prove2.me/submissions/fca0f963-7ba7-4c1b-9a8f-efebddc7553a

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (a b c d x D : ℝ) (hD : c * x + d = D) (hD0 : D ≠ 0) :
    HasDerivAt (fun y => (a * y + b) / (c * y + d)) ((a * D - (a * x + b) * c) / D ^ 2) x := by
  subst hD
  have hlin : ∀ a b : ℝ, HasDerivAt (fun y => a * y + b) a x := fun a b => by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  exact (hlin a b).div (hlin c d) hD0
end Aggmetrics.DataStream
