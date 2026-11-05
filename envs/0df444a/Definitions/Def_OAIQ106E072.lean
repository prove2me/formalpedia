-- Prove2me | Definitions.Def_OAIQ106E072
-- name    : OAIQ106E072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:55:24.535348+00:00
-- url     : https://prove2.me/theorems/81416af3-a11a-454a-919f-f8dee2e40133
-- title:
--   Definitions bundle OAIQ106E072 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.sourceChunk0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Source0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source0.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E062`, `OAIQ106E184`, `OAIQ106E070` and `OAIQ106E071` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E077`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E062
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E071

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk0 : Array (Integer.Sparse (Fin 3237)) := #[row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83, row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125, row126, row127]

end MUB6.Certificate.MixedData

end OAI
end


