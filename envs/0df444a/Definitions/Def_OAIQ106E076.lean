-- Prove2me | Definitions.Def_OAIQ106E076
-- name    : OAIQ106E076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:40:06.817671+00:00
-- url     : https://prove2.me/theorems/c0ed97b0-3f8a-464c-830e-1ea3fef4e342
-- title:
--   Definitions bundle OAIQ106E076 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.sourceChunk7`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Source7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source7.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E182`, `OAIQ106E184`, `OAIQ106E070` and `OAIQ106E071` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E077`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E182
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E071

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk7 : Array (Integer.Sparse (Fin 3237)) := #[row896, row897, row898, row899, row900, row901, row902, row903, row904, row905, row906, row907, row908, row909, row910, row911, row912, row913, row914, row915, row916, row917, row918, row919, row920, row921, row922, row923, row924, row925, row926, row927, row928, row929, row930, row931, row932, row933, row934, row935, row936, row937, row938, row939, row940, row941, row942, row943, row944, row945, row946, row947, row948, row949, row950, row951, row952, row953, row954, row955, row956, row957, row958, row959, row960, row961, row962, row963, row964, row965, row966, row967, row968, row969, row970, row971, row972, row973, row974, row975, row976, row977, row978, row979, row980, row981, row982, row983, row984, row985, row986, row987, row988, row989, row990, row991, row992, row993, row994, row995, row996, row997, row998, row999, row1000, row1001, row1002, row1003, row1004, row1005, row1006, row1007, row1008, row1009, row1010, row1011, row1012, row1013, row1014, row1015, row1016, row1017, row1018, row1019, row1020, row1021, row1022, row1023]

end MUB6.Certificate.MixedData

end OAI
end


