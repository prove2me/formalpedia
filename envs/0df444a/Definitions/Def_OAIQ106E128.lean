-- Prove2me | Definitions.Def_OAIQ106E128
-- name    : OAIQ106E128
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:11:11.813904+00:00
-- url     : https://prove2.me/theorems/ae862cd6-7e38-416b-a221-d6f6a05e39c5
-- title:
--   Definitions bundle OAIQ106E128 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 238 declarations of OpenAI's Lean: 238 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource734`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource735`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource736`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource737`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource738`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource739`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource740`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource741`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource742`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource743`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource744`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource745`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource746`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource747`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource748`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource749`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource750`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource751`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource752`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource753`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource754`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource755`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource756`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource757`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource758`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource759`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource76`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource760`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource761`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource762`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource763`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource764`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource765`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource766`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource767`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource768`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource769`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource770`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource771` and 198 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic4`, `MutuallyUnbiased_MixedSources_Arithmetic45`, `MutuallyUnbiased_MixedSources_Arithmetic46`, `MutuallyUnbiased_MixedSources_Arithmetic47`, `MutuallyUnbiased_MixedSources_Arithmetic48`, `MutuallyUnbiased_MixedSources_Arithmetic49`, `MutuallyUnbiased_MixedSources_Arithmetic5`, `MutuallyUnbiased_MixedSources_Arithmetic50`, `MutuallyUnbiased_MixedSources_Arithmetic51`, `MutuallyUnbiased_MixedSources_Arithmetic52`, `MutuallyUnbiased_MixedSources_Arithmetic53`, `MutuallyUnbiased_MixedSources_Arithmetic54`, `MutuallyUnbiased_MixedSources_Arithmetic55`, `MutuallyUnbiased_MixedSources_Arithmetic56`, `MutuallyUnbiased_MixedSources_Arithmetic57`, `MutuallyUnbiased_MixedSources_Arithmetic58`, `MutuallyUnbiased_MixedSources_Arithmetic59`, `MutuallyUnbiased_MixedSources_Arithmetic62`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e` and `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource8 (x : Master → ℝ) : ℝ :=
  (-1 : ℝ) * Sparse.eval nodeValue6 x + ((2 : ℝ) * Sparse.eval nodeValue494 x + ((1 : ℝ) * Sparse.eval nodeValue500 x + ((1 : ℝ) * Sparse.eval nodeValue524 x + ((2 : ℝ) * Sparse.eval nodeValue527 x + 0))))

noncomputable def reducedSource9 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5434 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((3 : ℝ) * Sparse.eval nodeValue5451 x + ((3 : ℝ) * Sparse.eval nodeValue5454 x + ((3 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource76 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1615 x + ((2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((2 : ℝ) * Sparse.eval nodeValue3355 x + ((2 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + 0))))))))))))))))))))

noncomputable def reducedSource78 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue1209 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource79 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue2562 x + ((2 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource733 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4489 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5093 x + ((2 : ℝ) * Sparse.eval nodeValue5094 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))))))

noncomputable def reducedSource734 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2503 x + ((2 : ℝ) * Sparse.eval nodeValue2504 x + ((2 : ℝ) * Sparse.eval nodeValue2505 x + ((2 : ℝ) * Sparse.eval nodeValue2515 x + ((2 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + 0))))))))))))))))))))

noncomputable def reducedSource735 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((2 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((4 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource736 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((2 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

noncomputable def reducedSource737 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((4 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + 0)))))))))))))

noncomputable def reducedSource738 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource739 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource740 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5055 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource741 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2458 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource742 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5246 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((3 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource743 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((3 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource744 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((3 : ℝ) * Sparse.eval nodeValue5104 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((6 : ℝ) * Sparse.eval nodeValue5259 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))

noncomputable def reducedSource745 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5247 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((6 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))

noncomputable def reducedSource746 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4438 x + ((2 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((4 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4885 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((4 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + 0)))))))))))))

noncomputable def reducedSource747 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((2 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((4 : ℝ) * Sparse.eval nodeValue2250 x + ((2 : ℝ) * Sparse.eval nodeValue2252 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((4 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2752 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + 0)))))))))))))

noncomputable def reducedSource748 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4248 x + ((4 : ℝ) * Sparse.eval nodeValue4249 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((8 : ℝ) * Sparse.eval nodeValue4802 x + ((4 : ℝ) * Sparse.eval nodeValue4831 x + ((4 : ℝ) * Sparse.eval nodeValue4888 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + 0)))))))

noncomputable def reducedSource749 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((3 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))

noncomputable def reducedSource750 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4068 x + ((3 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4079 x + ((6 : ℝ) * Sparse.eval nodeValue4080 x + ((6 : ℝ) * Sparse.eval nodeValue4083 x + ((6 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue4093 x + 0)))))))

noncomputable def reducedSource751 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2970 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3473 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3648 x + ((1 : ℝ) * Sparse.eval nodeValue3658 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource752 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource753 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2474 x + ((1 : ℝ) * Sparse.eval nodeValue2475 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource754 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource755 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3686 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource756 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2475 x + ((2 : ℝ) * Sparse.eval nodeValue3686 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

noncomputable def reducedSource757 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4812 x + ((1 : ℝ) * Sparse.eval nodeValue4813 x + ((1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4824 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5146 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5357 x + ((1 : ℝ) * Sparse.eval nodeValue5358 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource758 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource759 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource760 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((1 : ℝ) * Sparse.eval nodeValue4044 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource761 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3168 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource762 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource763 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource764 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource765 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource766 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource767 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource768 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue3168 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource769 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3743 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((1 : ℝ) * Sparse.eval nodeValue3829 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource770 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource771 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2611 x + ((1 : ℝ) * Sparse.eval nodeValue2919 x + ((1 : ℝ) * Sparse.eval nodeValue3195 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource772 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource773 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2945 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3863 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource774 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource775 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2920 x + ((1 : ℝ) * Sparse.eval nodeValue3865 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource776 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3195 x + ((1 : ℝ) * Sparse.eval nodeValue3863 x + ((1 : ℝ) * Sparse.eval nodeValue3865 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource777 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource778 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2919 x + ((1 : ℝ) * Sparse.eval nodeValue2920 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2945 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource779 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3712 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource780 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3970 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource781 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource782 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue3729 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource783 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource784 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue3717 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3729 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource785 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2578 x + ((1 : ℝ) * Sparse.eval nodeValue3717 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource786 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3712 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource787 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))))))))

noncomputable def reducedSource788 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3732 x + ((2 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((2 : ℝ) * Sparse.eval nodeValue3789 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((2 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((2 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + ((2 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

noncomputable def reducedSource789 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))))))))))))))

noncomputable def reducedSource790 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((2 : ℝ) * Sparse.eval nodeValue3706 x + ((2 : ℝ) * Sparse.eval nodeValue3782 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

noncomputable def reducedSource791 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5436 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))

noncomputable def reducedSource792 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

noncomputable def reducedSource793 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource794 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource795 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource796 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3824 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3911 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource797 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource798 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource799 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource80 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource81 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((2 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource82 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1378 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource83 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource84 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource85 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1209 x + ((1 : ℝ) * Sparse.eval nodeValue1378 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource86 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3492 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3545 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource87 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2052 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource88 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

noncomputable def reducedSource89 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3387 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((2 : ℝ) * Sparse.eval nodeValue3393 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource90 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue3387 x + ((3 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

noncomputable def reducedSource91 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((6 : ℝ) * Sparse.eval nodeValue5078 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

noncomputable def reducedSource92 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((6 : ℝ) * Sparse.eval nodeValue2485 x + ((3 : ℝ) * Sparse.eval nodeValue2519 x + ((3 : ℝ) * Sparse.eval nodeValue2601 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((3 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))

noncomputable def reducedSource93 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5252 x + ((6 : ℝ) * Sparse.eval nodeValue5261 x + ((3 : ℝ) * Sparse.eval nodeValue5268 x + ((3 : ℝ) * Sparse.eval nodeValue5296 x + ((2 : ℝ) * Sparse.eval nodeValue5312 x + 0)))))))

noncomputable def reducedSource94 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((6 : ℝ) * Sparse.eval nodeValue2712 x + ((3 : ℝ) * Sparse.eval nodeValue2726 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((3 : ℝ) * Sparse.eval nodeValue2755 x + ((3 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2790 x + ((3 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))))))))))

noncomputable def reducedSource95 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2292 x + ((3 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((1 : ℝ) * Sparse.eval nodeValue3636 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource800 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3736 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3823 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource801 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + 0)))))))))))))))

noncomputable def reducedSource802 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2392 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2394 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3347 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource803 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource804 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource805 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3374 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource806 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2872 x + ((1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource807 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource808 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2873 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource809 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2870 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource810 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource811 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource812 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource813 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4746 x + ((2 : ℝ) * Sparse.eval nodeValue4747 x + ((1 : ℝ) * Sparse.eval nodeValue4749 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5155 x + ((2 : ℝ) * Sparse.eval nodeValue5156 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5328 x + ((1 : ℝ) * Sparse.eval nodeValue5329 x + ((1 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((3 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))))))))

noncomputable def reducedSource814 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4817 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5287 x + ((2 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5407 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((3 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + 0)))))))))))))))))))))))))

noncomputable def reducedSource815 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource816 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4992 x + ((1 : ℝ) * Sparse.eval nodeValue4993 x + ((2 : ℝ) * Sparse.eval nodeValue4999 x + ((1 : ℝ) * Sparse.eval nodeValue5004 x + ((2 : ℝ) * Sparse.eval nodeValue5005 x + ((1 : ℝ) * Sparse.eval nodeValue5011 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

noncomputable def reducedSource817 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2378 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2384 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2912 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3337 x + ((2 : ℝ) * Sparse.eval nodeValue3342 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3946 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

noncomputable def reducedSource818 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2389 x + ((2 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((2 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((2 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

noncomputable def reducedSource819 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource820 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource821 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4791 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue5181 x + ((2 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5350 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))

noncomputable def reducedSource822 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3688 x + ((2 : ℝ) * Sparse.eval nodeValue3818 x + ((2 : ℝ) * Sparse.eval nodeValue3819 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((2 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

noncomputable def reducedSource823 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2074 x + ((2 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((2 : ℝ) * Sparse.eval nodeValue3524 x + ((2 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3734 x + ((2 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + 0))))))))))))))))))))

noncomputable def reducedSource824 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue4046 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource825 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2858 x + ((2 : ℝ) * Sparse.eval nodeValue3176 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource826 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3179 x + ((1 : ℝ) * Sparse.eval nodeValue3731 x + ((3 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource827 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2859 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3935 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource828 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3176 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3935 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource829 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((2 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource830 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource831 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3030 x + ((2 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3731 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource832 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2858 x + ((1 : ℝ) * Sparse.eval nodeValue2859 x + ((2 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource833 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((2 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((2 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))

noncomputable def reducedSource834 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3374 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3384 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4023 x + ((2 : ℝ) * Sparse.eval nodeValue4027 x + 0))))))))))))))))))))

noncomputable def reducedSource835 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource836 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2869 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource837 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3786 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource838 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2869 x + ((2 : ℝ) * Sparse.eval nodeValue2870 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource839 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3786 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource840 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))

noncomputable def reducedSource841 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2986 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3691 x + ((2 : ℝ) * Sparse.eval nodeValue3818 x + ((2 : ℝ) * Sparse.eval nodeValue3822 x + ((2 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((2 : ℝ) * Sparse.eval nodeValue4038 x + 0))))))))))))))))))))

noncomputable def reducedSource842 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3806 x + ((2 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + 0))))))))))))))))))))

noncomputable def reducedSource843 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5085 x + ((2 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((2 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5407 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + 0))))))))))))))))))

noncomputable def reducedSource844 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3996 x + 0))))))))))))))))))))

noncomputable def reducedSource845 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))

noncomputable def reducedSource846 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource847 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue3431 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3743 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource848 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource849 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource850 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource851 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4797 x + ((1 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4825 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5132 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5350 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5362 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource852 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2073 x + ((1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3726 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((1 : ℝ) * Sparse.eval nodeValue3829 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource853 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue3499 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3700 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((1 : ℝ) * Sparse.eval nodeValue3822 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource854 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource855 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource856 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource857 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5082 x + ((1 : ℝ) * Sparse.eval nodeValue5083 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5091 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5146 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5357 x + ((1 : ℝ) * Sparse.eval nodeValue5358 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource858 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3968 x + ((1 : ℝ) * Sparse.eval nodeValue3970 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource859 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3441 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource860 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue4044 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource861 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2977 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource862 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource863 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource864 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3394 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((2 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3964 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((2 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

noncomputable def reducedSource865 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

noncomputable def reducedSource866 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3787 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3915 x + ((2 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

noncomputable def reducedSource867 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))

noncomputable def reducedSource868 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource869 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource870 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource871 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4849 x + ((1 : ℝ) * Sparse.eval nodeValue4850 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4861 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue5183 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5399 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource872 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3728 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource873 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3501 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource874 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource875 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource876 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource877 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2506 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3939 x + ((1 : ℝ) * Sparse.eval nodeValue3968 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource878 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3384 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource879 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource880 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2869 x + ((1 : ℝ) * Sparse.eval nodeValue2871 x + ((1 : ℝ) * Sparse.eval nodeValue2873 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource881 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2853 x + ((1 : ℝ) * Sparse.eval nodeValue2856 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3370 x + ((1 : ℝ) * Sparse.eval nodeValue3372 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3653 x + ((1 : ℝ) * Sparse.eval nodeValue3666 x + ((1 : ℝ) * Sparse.eval nodeValue3778 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((3 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource882 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5407 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource883 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource884 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((1 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource885 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource886 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5064 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5181 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5350 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource887 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((2 : ℝ) * Sparse.eval nodeValue3936 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

noncomputable def reducedSource888 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3443 x + ((2 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3750 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3946 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + 0))))))))))))))))))))

noncomputable def reducedSource889 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource890 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5183 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5399 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5402 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))

noncomputable def reducedSource891 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3501 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3785 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4023 x + 0))))))))))))))))))))

noncomputable def reducedSource892 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue3783 x + ((2 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + 0))))))))))))))))))))

noncomputable def reducedSource893 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3689 x + ((2 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource894 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3923 x + ((1 : ℝ) * Sparse.eval nodeValue3969 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource895 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource896 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4848 x + ((2 : ℝ) * Sparse.eval nodeValue4849 x + ((2 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5382 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))

noncomputable def reducedSource897 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource898 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource899 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3921 x + ((1 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource900 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))

noncomputable def reducedSource901 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5065 x + ((2 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))

noncomputable def reducedSource902 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((2 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((2 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + 0)))))))))))))))))))

noncomputable def reducedSource903 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5407 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))

noncomputable def reducedSource904 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + 0))))))))))))))))))))

noncomputable def reducedSource905 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource906 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource907 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3790 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource908 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource909 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3687 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3702 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource910 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource911 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource912 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5047 x + ((2 : ℝ) * Sparse.eval nodeValue5050 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0)))))))))))))))))

noncomputable def reducedSource913 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2449 x + ((2 : ℝ) * Sparse.eval nodeValue2452 x + ((2 : ℝ) * Sparse.eval nodeValue2462 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3678 x + ((2 : ℝ) * Sparse.eval nodeValue3683 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3942 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + 0)))))))))))))))))

noncomputable def reducedSource914 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))

noncomputable def reducedSource915 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3793 x + ((2 : ℝ) * Sparse.eval nodeValue3794 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))

noncomputable def reducedSource916 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource917 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource918 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5341 x + ((1 : ℝ) * Sparse.eval nodeValue5344 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))))))))))

noncomputable def reducedSource919 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue1990 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3678 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3746 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource920 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))

noncomputable def reducedSource921 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource922 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((4 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((4 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))

noncomputable def reducedSource923 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

noncomputable def reducedSource924 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource925 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3952 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource926 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5346 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))

noncomputable def reducedSource927 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2467 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3341 x + ((1 : ℝ) * Sparse.eval nodeValue3344 x + ((1 : ℝ) * Sparse.eval nodeValue3357 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3942 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4050 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource928 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource929 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource930 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource931 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource932 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource933 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource934 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4996 x + ((2 : ℝ) * Sparse.eval nodeValue5003 x + ((2 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0)))))))))))))))

noncomputable def reducedSource935 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((4 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5413 x + ((4 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5468 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))

noncomputable def reducedSource936 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3631 x + ((4 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((2 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3950 x + ((4 : ℝ) * Sparse.eval nodeValue3958 x + ((4 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((2 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0))))))))))))

noncomputable def reducedSource937 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5018 x + ((2 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5023 x + ((4 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5467 x + ((8 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))

noncomputable def reducedSource938 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5206 x + ((4 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5420 x + ((4 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((4 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))

noncomputable def reducedSource939 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((2 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2774 x + ((4 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((4 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((2 : ℝ) * Sparse.eval nodeValue3870 x + ((4 : ℝ) * Sparse.eval nodeValue3881 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0))))))))))))

noncomputable def reducedSource940 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4860 x + ((1 : ℝ) * Sparse.eval nodeValue4862 x + ((4 : ℝ) * Sparse.eval nodeValue4874 x + ((8 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5398 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))

noncomputable def reducedSource941 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource942 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource943 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4828 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource944 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5127 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0)))))))))))))))))

noncomputable def reducedSource945 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3513 x + ((2 : ℝ) * Sparse.eval nodeValue3514 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((2 : ℝ) * Sparse.eval nodeValue3795 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + 0)))))))))))))))))

noncomputable def reducedSource946 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4778 x + ((4 : ℝ) * Sparse.eval nodeValue4782 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5344 x + ((4 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((2 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))

noncomputable def reducedSource947 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))

noncomputable def reducedSource954 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue5155 x + ((2 : ℝ) * Sparse.eval nodeValue5166 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5383 x + ((6 : ℝ) * Sparse.eval nodeValue5412 x + ((6 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource992 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5398 x + ((8 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((8 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((4 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


