-- Prove2me | Definitions.Def_OAIQ106E085
-- name    : OAIQ106E085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:51:06.669414+00:00
-- url     : https://prove2.me/theorems/16880d88-64ec-4db3-8cb8-237fa05cd26a
-- title:
--   Definitions bundle OAIQ106E085 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.codes`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Coordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Coordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E080`, `OAIQ106E082`, `OAIQ106E083` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E086`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E080
import Definitions.Def_OAIQ106E082
import Definitions.Def_OAIQ106E083
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def codes (i : Fin 5502) : Code :=
  ((#[codeChunk0, codeChunk1, codeChunk2, codeChunk3, codeChunk4, codeChunk5, codeChunk6, codeChunk7, codeChunk8, codeChunk9, codeChunk10, codeChunk11, codeChunk12, codeChunk13, codeChunk14, codeChunk15, codeChunk16, codeChunk17, codeChunk18, codeChunk19, codeChunk20, codeChunk21, codeChunk22, codeChunk23, codeChunk24, codeChunk25, codeChunk26, codeChunk27, codeChunk28, codeChunk29, codeChunk30, codeChunk31, codeChunk32, codeChunk33, codeChunk34, codeChunk35, codeChunk36, codeChunk37, codeChunk38, codeChunk39, codeChunk40, codeChunk41, codeChunk42, codeChunk43, codeChunk44, codeChunk45, codeChunk46, codeChunk47, codeChunk48, codeChunk49, codeChunk50, codeChunk51, codeChunk52, codeChunk53, codeChunk54, codeChunk55, codeChunk56, codeChunk57, codeChunk58, codeChunk59, codeChunk60, codeChunk61, codeChunk62, codeChunk63, codeChunk64, codeChunk65, codeChunk66, codeChunk67, codeChunk68, codeChunk69, codeChunk70, codeChunk71, codeChunk72, codeChunk73, codeChunk74, codeChunk75, codeChunk76, codeChunk77, codeChunk78, codeChunk79, codeChunk80, codeChunk81, codeChunk82, codeChunk83, codeChunk84, codeChunk85])[i.val / 64]!)[i.val % 64]!

end MUB6.Certificate.MixedSemantics

end OAI
end


