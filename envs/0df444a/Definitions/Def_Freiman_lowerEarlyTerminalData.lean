-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalData
-- name    : Freiman_lowerEarlyTerminalData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:36:25.154343+00:00
-- url     : https://prove2.me/theorems/fca7e750-4a1c-419f-9932-47ef76dc518f
-- title:
--   Freiman.lowerEarlyTerminalData
-- statement:
--   Assemble the four authoritative source catalog families without conflating the487 short residuals and920 terminal extension records. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalData.

import Definitions.Def_Freiman_lowerEarlyTerminalDataEarly3
import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Definitions.Def_Freiman_lowerEarlyTerminalDataState2
import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
namespace Freiman
def lowerEarlyTerminalCatalog (i : Fin 4) : LowerEarlyTerminalCatalog :=
  if i=0 then lowerEarlyTerminalEarly3 else if i=1 then lowerEarlyTerminalState1 else if i=2 then lowerEarlyTerminalState2 else lowerEarlyTerminalTerminal3
end Freiman


