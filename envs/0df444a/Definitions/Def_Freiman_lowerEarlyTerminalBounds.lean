-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalBounds
-- name    : Freiman_lowerEarlyTerminalBounds
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:28:07.812428+00:00
-- url     : https://prove2.me/theorems/3443d446-5b38-450b-b5f7-d6feec37e1f1
-- title:
--   Freiman.lowerEarlyTerminalBounds
-- statement:
--   The1,238 exact distinct scalar inequalities used by the four catalog files; rational coordinates preserve all strictness bits. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalBounds.

import Definitions.Def_Freiman_lowerEarlyTerminalBounds01
import Definitions.Def_Freiman_lowerEarlyTerminalBounds02
import Definitions.Def_Freiman_lowerEarlyTerminalBounds03
import Definitions.Def_Freiman_lowerEarlyTerminalBounds04
import Definitions.Def_Freiman_lowerEarlyTerminalBounds05
import Definitions.Def_Freiman_lowerEarlyTerminalBounds06
import Definitions.Def_Freiman_lowerEarlyTerminalBounds07
import Definitions.Def_Freiman_lowerEarlyTerminalBounds08
import Definitions.Def_Freiman_lowerEarlyTerminalBounds09
namespace Freiman
def lowerEarlyTerminalBounds : List CertBound :=
  lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08 ++ lowerEarlyTerminalBounds09
end Freiman


