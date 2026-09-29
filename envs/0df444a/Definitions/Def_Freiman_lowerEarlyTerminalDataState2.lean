-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalDataState2
-- name    : Freiman_lowerEarlyTerminalDataState2
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:35:12.418419+00:00
-- url     : https://prove2.me/theorems/af1af155-2ffa-41d3-a3d2-2653e37bd9e3
-- title:
--   Freiman.lowerEarlyTerminalDataState2
-- statement:
--   Assemble the four authoritative source catalog families without conflating the487 short residuals and920 terminal extension records. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalDataState2.

import Definitions.Def_Freiman_lowerEarlyTerminalGoalsState2
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState2
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsState2
namespace Freiman
def lowerEarlyTerminalState2 : LowerEarlyTerminalCatalog :=
  ⟨[2], ⟨(1/3),(1/2),(3/4),(4/5)⟩, lowerEarlyTerminalBounds, lowerEarlyTerminalGoalsState2, lowerEarlyTerminalPairsState2, lowerEarlyTerminalRecordsState2⟩
end Freiman


