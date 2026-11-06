-- Prove2me | Definitions.Def_OAIQ106E157
-- name    : OAIQ106E157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:19:31.684483+00:00
-- url     : https://prove2.me/theorems/041e4a80-fff3-410f-bc27-aa221b1fafad
-- title:
--   Definitions bundle OAIQ106E157 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.TaoArithmetic.normalize`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Tao_TaoSparse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoSparse.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E196` and `OAIQ106E140` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.TaoCertificate.combined377_zero_e`, `OAI.MUB6.TaoCertificate.combined396_zero_e`, `OAI.MUB6.TaoCertificate.combined414_zero_e`, `OAI.MUB6.TaoCertificate.combined438_zero_e`, `OAI.MUB6.TaoCertificate.combined455_zero_e`, `OAI.MUB6.TaoCertificate.combined474_zero_e` and `OAI.MUB6.complete_family_square_not_hadamard_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoSparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def normalize : Sparse → Sparse
  | [] => []
  | p :: ps => if p.2 = 0 then normalize ps
      else Certificate.Integer.Sparse.merge [p] (normalize ps)

end MUB6.TaoArithmetic

end

end OAI
end


