-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
-- name    : Freiman_lowerEarlyTerminalDataTerminal3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:34:44.587981+00:00
-- url     : https://prove2.me/theorems/56b675f0-6e2c-4c01-aa91-22241dd2b32b
-- title:
--   Freiman.lowerEarlyTerminalDataTerminal3
-- statement:
--   Assemble the four authoritative source catalog families without conflating the487 short residuals and920 terminal extension records. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_terminal/geometry_certificate.json:952 records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_terminal/geometry_certificate.json:952 records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3.

import Definitions.Def_Freiman_lowerEarlyTerminalGoalsTerminal3
import Definitions.Def_Freiman_lowerEarlyTerminalPairsTerminal3
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsTerminal3
namespace Freiman
def lowerEarlyTerminalTerminal3 : LowerEarlyTerminalCatalog :=
  ⟨[3], ⟨(1/4),(1/3),(3/4),(4/5)⟩, lowerEarlyTerminalBounds, lowerEarlyTerminalGoalsTerminal3, lowerEarlyTerminalPairsTerminal3, lowerEarlyTerminalRecordsTerminal3⟩
end Freiman


