-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalDataState1
-- name    : Freiman_lowerEarlyTerminalDataState1
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:35:00.094116+00:00
-- url     : https://prove2.me/theorems/54e2d7a0-80aa-4522-bc5c-36e94e419857
-- title:
--   Freiman.lowerEarlyTerminalDataState1
-- statement:
--   Assemble the four authoritative source catalog families without conflating the487 short residuals and920 terminal extension records. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalDataState1.

import Definitions.Def_Freiman_lowerEarlyTerminalGoalsState1
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState1
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState1
namespace Freiman
def lowerEarlyTerminalState1 : LowerEarlyTerminalCatalog :=
  ⟨[1], ⟨(1/2),(4/5),(3/4),(4/5)⟩, lowerEarlyTerminalBounds, lowerEarlyTerminalGoalsState1, lowerEarlyTerminalPairsState1, lowerEarlyTerminalRecordsState1⟩
end Freiman


