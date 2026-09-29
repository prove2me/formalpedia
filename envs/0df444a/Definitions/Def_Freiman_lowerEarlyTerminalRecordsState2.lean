-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalRecordsState2
-- name    : Freiman_lowerEarlyTerminalRecordsState2
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:33:16.009389+00:00
-- url     : https://prove2.me/theorems/c9a5d727-310f-4807-840b-d789c21c44da
-- title:
--   Freiman.lowerEarlyTerminalRecordsState2
-- statement:
--   Typed, losslessly transcribed RecordsState2 data: exact source goal specifications, conflicting bound pairs or source residual records, with range-checked references. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalRecordsState2.

import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState201
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState202
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState203
namespace Freiman
def lowerEarlyTerminalRecordsState2 : List LowerEarlyTerminalRecord :=
  lowerEarlyTerminalRecordsState201 ++ lowerEarlyTerminalRecordsState202 ++ lowerEarlyTerminalRecordsState203
end Freiman


