-- Prove2me | Definitions.Def_OAIQ084L030
-- name    : OAIQ084L030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:33:52.327759+00:00
-- url     : https://prove2.me/theorems/1be25e2a-04e1-4689-8fa8-9c147f3ee41e
-- title:
--   Definitions bundle OAIQ084L030 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.LaughlinFock.fourYData_10`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate10Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate10Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.LaughlinFock.fourYChecked_10`; the proofs of `OAI.LaughlinFock.fourYChecked_10` and `OAI.LaughlinFock.integer_certificate_10`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_10 : Matrix (CopyLabel 10) (CopyLabel 10) ℚ :=
  copyMatrixData 10 [
    [(737670548859399948830388711147/33554432000000000000000000), (-340762940414160772908009142467/134217728000000000000000000), (148518328795926257133899451/134217728000000000000000), (-424730358650114657260778608119/536870912000000000000000000), (74331768409382616339850430283/134217728000000000000000000)],
    [(-340762940414160772908009142467/134217728000000000000000000), (6753716923485661803328277187/67108864000000000000000000), (-133847515145750760226034487/1342177280000000000000000), (27875776847130353195239319289/214748364800000000000000000), (-62712565299322420555264659867/268435456000000000000000000)],
    [(148518328795926257133899451/134217728000000000000000), (-133847515145750760226034487/1342177280000000000000000), (4916058814322941309449723117/107374182400000000000000000), (-8781593118050446480941197751/214748364800000000000000000), (79913088812449654011001179/1342177280000000000000000)],
    [(-424730358650114657260778608119/536870912000000000000000000), (27875776847130353195239319289/214748364800000000000000000), (-8781593118050446480941197751/214748364800000000000000000), (88212964072712605466404249449/4294967296000000000000000000), (-4590411174217141231271545953/1073741824000000000000000000)],
    [(74331768409382616339850430283/134217728000000000000000000), (-62712565299322420555264659867/268435456000000000000000000), (79913088812449654011001179/1342177280000000000000000), (-4590411174217141231271545953/1073741824000000000000000000), (-34263985364968403855161804941/268435456000000000000000000)]
  ]

end LaughlinFock
end

end OAI
end


