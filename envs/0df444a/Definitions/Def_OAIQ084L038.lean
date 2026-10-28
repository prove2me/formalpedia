-- Prove2me | Definitions.Def_OAIQ084L038
-- name    : OAIQ084L038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:35:31.007994+00:00
-- url     : https://prove2.me/theorems/7382c2b1-65a3-4e1e-8e2f-7b09c00a4d61
-- title:
--   Definitions bundle OAIQ084L038 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourYData_8`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate08Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate08Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_8`; the proofs of `OAI.LaughlinFock.fourYChecked_8` and `OAI.LaughlinFock.integer_certificate_8`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

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

 

def fourYData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [(-63725659480009131775992546879/536870912000000000000000000), (-1915756407095537127488603541/268435456000000000000000000), (5848046872621070751629176509/536870912000000000000000000), (-15409311511841483890426595631/2147483648000000000000000000)],
    [(-1915756407095537127488603541/268435456000000000000000000), (-20669734241111819247651968649/7516192768000000000000000000), (9455940384238314087831042759/3758096384000000000000000000), (-12382701644617792221325809759/4294967296000000000000000000)],
    [(5848046872621070751629176509/536870912000000000000000000), (9455940384238314087831042759/3758096384000000000000000000), (-2472410179928723052502001181/1073741824000000000000000000), (1770955193734196297743289949/536870912000000000000000000)],
    [(-15409311511841483890426595631/2147483648000000000000000000), (-12382701644617792221325809759/4294967296000000000000000000), (1770955193734196297743289949/536870912000000000000000000), (-178020445962132587387054522433/17179869184000000000000000000)]
  ]

end LaughlinFock
end

end OAI
end


