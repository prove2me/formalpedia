-- Prove2me | Definitions.Def_OAIQ084L042
-- name    : OAIQ084L042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:17.066242+00:00
-- url     : https://prove2.me/theorems/89ee2434-40fa-4662-8492-0a44be04ac02
-- title:
--   Definitions bundle OAIQ084L042 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourZData_9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate09Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate09Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.LaughlinFock.integer_certificate_9`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_9 : Matrix (CopyLabel 9) (CopyLabel 9) ℚ :=
  copyMatrixData 9 [
    [40320, 0, 0, -630, (8505/2)],
    [0, 540, -135, 0, (2835/8)],
    [0, -135, (135/4), 0, (-2835/32)],
    [-630, 0, 0, (315/32), (-8505/128)],
    [(8505/2), (2835/8), (-2835/32), (-8505/128), (348705/512)]
  ]

end LaughlinFock
end

end OAI
end


