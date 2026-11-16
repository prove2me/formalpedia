-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_driverInit
-- name    : MaxMinFracSched_Supplement_driverInit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:21:22.471868+00:00
-- url     : https://prove2.me/theorems/0613942a-d18e-45aa-beea-704221e74896
-- title:
--   Initial driver state
-- statement:
--   At the start of an event-driven run the machine is in the published real RAM's initial state on the empty input (every register, pointer and memory cell $0$). No operation has run, no batch has arrived, no event is announced, nothing has been served, and neither flag is set.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8.1.6, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Supplement_DriverState

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **The initial driver state.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8.1.6, p.49 (PDF p.51): "or 0 at the first arrival, at which we also initialize".

The machine is in the initial state of the published real RAM on the empty input (all registers,
pointers and memory cells `0`); no operation has run, no batch has arrived, no event is announced
(the empty output), and nothing is served. -/
noncomputable def driverInit : DriverState :=
  ⟨initState [], 0, 0, [], [], [], false, false⟩

end Supplement

end MaxMinFracSched


