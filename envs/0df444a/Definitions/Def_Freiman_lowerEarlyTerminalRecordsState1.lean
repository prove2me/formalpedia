-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalRecordsState1
-- name    : Freiman_lowerEarlyTerminalRecordsState1
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:33:09.325099+00:00
-- url     : https://prove2.me/theorems/f10e552e-04e4-4bf2-b9ef-a0739019debc
-- title:
--   Freiman.lowerEarlyTerminalRecordsState1
-- statement:
--   Typed, losslessly transcribed RecordsState1 data: exact source goal specifications, conflicting bound pairs or source residual records, with range-checked references. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalRecordsState1.

import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState101
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState102
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState103
namespace Freiman
def lowerEarlyTerminalRecordsState1 : List LowerEarlyTerminalRecord :=
  lowerEarlyTerminalRecordsState101 ++ lowerEarlyTerminalRecordsState102 ++ lowerEarlyTerminalRecordsState103
end Freiman


