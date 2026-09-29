-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalDataEarly3
-- name    : Freiman_lowerEarlyTerminalDataEarly3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:33:03.832328+00:00
-- url     : https://prove2.me/theorems/3e9fec6e-701b-44fc-a479-6930a3419965
-- title:
--   Freiman.lowerEarlyTerminalDataEarly3
-- statement:
--   Assemble the four authoritative source catalog families without conflating the487 short residuals and920 terminal extension records. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/residual_geometry_certificate.json:487 records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/residual_geometry_certificate.json:487 records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalDataEarly3.

import Definitions.Def_Freiman_lowerEarlyTerminalGoalsEarly3
import Definitions.Def_Freiman_lowerEarlyTerminalPairsEarly3
import Definitions.Def_Freiman_lowerEarlyTerminalRecordsEarly3
namespace Freiman
def lowerEarlyTerminalEarly3 : LowerEarlyTerminalCatalog :=
  ⟨[3], ⟨(1/4),(1/3),(3/4),(4/5)⟩, lowerEarlyTerminalBounds, lowerEarlyTerminalGoalsEarly3, lowerEarlyTerminalPairsEarly3, lowerEarlyTerminalRecordsEarly3⟩
end Freiman


