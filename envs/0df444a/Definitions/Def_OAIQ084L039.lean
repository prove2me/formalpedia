-- Prove2me | Definitions.Def_OAIQ084L039
-- name    : OAIQ084L039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:21.048048+00:00
-- url     : https://prove2.me/theorems/ffb4e735-5407-4263-8117-886360659978
-- title:
--   Definitions bundle OAIQ084L039 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourYData_9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate09Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate09Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYLower_9`; the proofs of `OAI.LaughlinFock.fourYLower_9` and `OAI.LaughlinFock.integer_certificate_9`.
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

 

def fourYData_9 : Matrix (CopyLabel 9) (CopyLabel 9) ℚ :=
  copyMatrixData 9 [
    [(-146091607413928872790325971761/268435456000000000000000000), (-27122971776637241097052043481/536870912000000000000000000), (260469020419292216479075761/53687091200000000000000000), (30789416395436608069256092953/2147483648000000000000000000), (-129703291268636859530657931099/536870912000000000000000000)],
    [(-27122971776637241097052043481/536870912000000000000000000), (-128380238690076998480031524721/7516192768000000000000000000), (39773187663702578771741264079/3758096384000000000000000000), (-1837610439668880684708642399/171798691840000000000000000), (-20806144524092430933966807651/1073741824000000000000000000)],
    [(260469020419292216479075761/53687091200000000000000000), (39773187663702578771741264079/3758096384000000000000000000), (-46478716744801148895226746231/7516192768000000000000000000), (1660933205203877918300823867/268435456000000000000000000), (7156024769090901250266984873/536870912000000000000000000)],
    [(30789416395436608069256092953/2147483648000000000000000000), (-1837610439668880684708642399/171798691840000000000000000), (1660933205203877918300823867/268435456000000000000000000), (-105495675446941487863399344237/17179869184000000000000000000), (-85051785275352886328867049021/4294967296000000000000000000)],
    [(-129703291268636859530657931099/536870912000000000000000000), (-20806144524092430933966807651/1073741824000000000000000000), (7156024769090901250266984873/536870912000000000000000000), (-85051785275352886328867049021/4294967296000000000000000000), (-99131997774302568689042771217/1073741824000000000000000000)]
  ]

end LaughlinFock
end

end OAI
end


