-- Prove2me | Definitions.Def_OAIQ084L036
-- name    : OAIQ084L036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:35:06.186658+00:00
-- url     : https://prove2.me/theorems/4028cc05-12db-4925-8db3-629b4da14b94
-- title:
--   Definitions bundle OAIQ084L036 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourYData_5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate05Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate05Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_5`; the proofs of `OAI.LaughlinFock.certificate_four` and `OAI.LaughlinFock.fourYChecked_5`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate05Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate05 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ :=
  copyMatrixData 5 [
    [(-2024172058688009719584426783/60129542144000000000000000000), (61749543313564923991586775801/601295421440000000000000000000), (-371682523763530720573033623/12025908428800000000000000000)],
    [(61749543313564923991586775801/601295421440000000000000000000), (-81625478502088057676049676411/1202590842880000000000000000000), (6370708288009007294968493697/120259084288000000000000000000)],
    [(-371682523763530720573033623/12025908428800000000000000000), (6370708288009007294968493697/120259084288000000000000000000), (-400615328776296560234415701/3006477107200000000000000000)]
  ]

end LaughlinFock
end

end OAI
end


