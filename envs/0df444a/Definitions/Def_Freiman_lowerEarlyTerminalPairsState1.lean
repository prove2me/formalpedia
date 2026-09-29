-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalPairsState1
-- name    : Freiman_lowerEarlyTerminalPairsState1
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:31:28.957424+00:00
-- url     : https://prove2.me/theorems/76db2f0b-de36-4ee8-9312-f9270fc40d4f
-- title:
--   Freiman.lowerEarlyTerminalPairsState1
-- statement:
--   Typed, losslessly transcribed PairsState1 data: exact source goal specifications, conflicting bound pairs or source residual records, with range-checked references. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/extension_1.json:487 early and920 terminal records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalPairsState1.

import Definitions.Def_Freiman_lowerEarlyTerminalPairsState101
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState102
import Definitions.Def_Freiman_lowerEarlyTerminalPairsState103
namespace Freiman
def lowerEarlyTerminalPairsState1 : List LowerEarlyTerminalPair :=
  lowerEarlyTerminalPairsState101 ++ lowerEarlyTerminalPairsState102 ++ lowerEarlyTerminalPairsState103
end Freiman


