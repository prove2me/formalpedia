-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalPairsState2
-- name    : Freiman_lowerEarlyTerminalPairsState2
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:31:01.676986+00:00
-- url     : https://prove2.me/theorems/4f6f00f1-3101-48ce-9be0-f7d68277533c
-- title:
--   Freiman.lowerEarlyTerminalPairsState2
-- statement:
--   Typed, losslessly transcribed PairsState2 data: exact source goal specifications, conflicting bound pairs or source residual records, with range-checked references. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_2.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalPairsState2.

import Definitions.Def_Freiman_lowerEarlyTerminalPairsState201
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState202
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState203
namespace Freiman
def lowerEarlyTerminalPairsState2 : List LowerEarlyTerminalPair :=
  lowerEarlyTerminalPairsState201 ++ lowerEarlyTerminalPairsState202 ++ lowerEarlyTerminalPairsState203
end Freiman


