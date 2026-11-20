-- Prove2me | solution 1 for Aggmetrics.DataStream.accuracy_midpoint_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:48.745183+00:00
-- url     : https://prove2.me/submissions/4c291f97-c6bb-4a61-80bc-b266d0e39d1d

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R0 S0 π0 R1 S1 π1 : ℝ) :
    accuracy R1 S1 π1 - accuracy R0 S0 π0
      = ((π0 + π1) / 2) * (R1 - R0) + (1 - (π0 + π1) / 2) * (S1 - S0)
        + ((R0 + R1) / 2 - (S0 + S1) / 2) * (π1 - π0) := by
  unfold accuracy
  ring
end Aggmetrics.DataStream
