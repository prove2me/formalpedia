-- Prove2me | Definitions.Def_OAIQ084L037
-- name    : OAIQ084L037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:35:48.706461+00:00
-- url     : https://prove2.me/theorems/88adb4bd-9dea-47b9-9642-73de135ca7ab
-- title:
--   Definitions bundle OAIQ084L037 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourYData_7`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate07Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate07Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_7`; the proofs of `OAI.LaughlinFock.certificate_four` and `OAI.LaughlinFock.fourYChecked_7`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

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

 

def fourYData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [(-166434639714168948577730130927/3758096384000000000000000000), (45995705370248318526416296167/7516192768000000000000000000), (-106335364725988709134966359/53687091200000000000000000), (-51594657218957307370313483247/4294967296000000000000000000)],
    [(45995705370248318526416296167/7516192768000000000000000000), (-87211931042683137626019530763/75161927680000000000000000000), (1568403660783923680978370343/3006477107200000000000000000), (3815628101661385334514451191/1717986918400000000000000000)],
    [(-106335364725988709134966359/53687091200000000000000000), (1568403660783923680978370343/3006477107200000000000000000), (-11751684800182621092199856481/30064771072000000000000000000), (-10949361788140579505956340379/8589934592000000000000000000)],
    [(-51594657218957307370313483247/4294967296000000000000000000), (3815628101661385334514451191/1717986918400000000000000000), (-10949361788140579505956340379/8589934592000000000000000000), (-148920474389511901767358542711/34359738368000000000000000000)]
  ]

end LaughlinFock
end

end OAI
end


