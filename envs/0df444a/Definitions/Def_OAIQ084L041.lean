-- Prove2me | Definitions.Def_OAIQ084L041
-- name    : OAIQ084L041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:48.437252+00:00
-- url     : https://prove2.me/theorems/cdd55b6e-7918-4ffd-aa83-9593960defbf
-- title:
--   Definitions bundle OAIQ084L041 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.LaughlinFock.fourZData_5`, `OAI.LaughlinFock.fourZData_7`, `OAI.LaughlinFock.fourZData_8`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate05Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate05Data.lean), [`LaughlinFock_Certificate07Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate07Data.lean), [`LaughlinFock_Certificate08Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate08Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.LaughlinFock.certificate_four` and `OAI.LaughlinFock.integer_certificate_8`.
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



def fourZData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ :=
  copyMatrixData 5 [
    [24, -6, (15/2)],
    [-6, (3/2), (-15/8)],
    [(15/2), (-15/8), (75/32)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [720, 0, -45, (315/2)],
    [0, 0, 0, 0],
    [-45, 0, (45/16), (-315/32)],
    [(315/2), 0, (-315/32), (2205/64)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [0, 0, 0, 0],
    [0, 90, -45, (315/8)],
    [0, -45, (45/2), (-315/16)],
    [0, (315/8), (-315/16), (2205/128)]
  ]

end LaughlinFock
end

end OAI
end


