-- Prove2me | Definitions.Def_OAIQ106E127
-- name    : OAIQ106E127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:11:22.4731+00:00
-- url     : https://prove2.me/theorems/757b28d3-051f-4a86-8741-fead4cdc9dd0
-- title:
--   Definitions bundle OAIQ106E127 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 375 declarations of OpenAI's Lean: 375 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource396`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource398`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource399`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource4`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource400`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource401`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource402`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource403`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource404`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource405`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource406`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource407`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource408`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource409`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource41`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource410`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource411`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource412`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource413`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource414`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource415`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource416`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource417`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource418`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource419`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource42`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource420`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource421`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource422`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource424`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource425`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource426`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource427`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource428`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource429`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource43`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource430`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource431`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource432` and 335 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic2`, `MutuallyUnbiased_MixedSources_Arithmetic24`, `MutuallyUnbiased_MixedSources_Arithmetic25`, `MutuallyUnbiased_MixedSources_Arithmetic26`, `MutuallyUnbiased_MixedSources_Arithmetic27`, `MutuallyUnbiased_MixedSources_Arithmetic28`, `MutuallyUnbiased_MixedSources_Arithmetic29`, `MutuallyUnbiased_MixedSources_Arithmetic3`, `MutuallyUnbiased_MixedSources_Arithmetic30`, `MutuallyUnbiased_MixedSources_Arithmetic31`, `MutuallyUnbiased_MixedSources_Arithmetic32`, `MutuallyUnbiased_MixedSources_Arithmetic33`, `MutuallyUnbiased_MixedSources_Arithmetic34`, `MutuallyUnbiased_MixedSources_Arithmetic35`, `MutuallyUnbiased_MixedSources_Arithmetic36`, `MutuallyUnbiased_MixedSources_Arithmetic37`, `MutuallyUnbiased_MixedSources_Arithmetic38`, `MutuallyUnbiased_MixedSources_Arithmetic39`, `MutuallyUnbiased_MixedSources_Arithmetic4`, `MutuallyUnbiased_MixedSources_Arithmetic40`, `MutuallyUnbiased_MixedSources_Arithmetic41`, `MutuallyUnbiased_MixedSources_Arithmetic42`, `MutuallyUnbiased_MixedSources_Arithmetic43`, `MutuallyUnbiased_MixedSources_Arithmetic44`, `MutuallyUnbiased_MixedSources_Arithmetic45`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e` and `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`.
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

noncomputable def reducedSource4 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))

noncomputable def reducedSource5 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((4 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((2 : ℝ) * Sparse.eval nodeValue3971 x + ((4 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((4 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4015 x + ((2 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4055 x + 0))))))))))))

noncomputable def reducedSource6 (x : Master → ℝ) : ℝ :=
  (-1 : ℝ) * Sparse.eval nodeValue7 x + ((1 : ℝ) * Sparse.eval nodeValue378 x + ((1 : ℝ) * Sparse.eval nodeValue514 x + ((1 : ℝ) * Sparse.eval nodeValue518 x + ((1 : ℝ) * Sparse.eval nodeValue521 x + ((1 : ℝ) * Sparse.eval nodeValue526 x + ((1 : ℝ) * Sparse.eval nodeValue527 x + 0))))))

noncomputable def reducedSource7 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5488 x + ((4 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5496 x + 0))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource41 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1462 x + ((2 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource42 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1047 x + ((2 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource43 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1461 x + ((2 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource44 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1031 x + ((2 : ℝ) * Sparse.eval nodeValue1458 x + ((1 : ℝ) * Sparse.eval nodeValue1461 x + ((1 : ℝ) * Sparse.eval nodeValue1462 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource45 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource46 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1066 x + ((1 : ℝ) * Sparse.eval nodeValue1067 x + ((1 : ℝ) * Sparse.eval nodeValue1068 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource47 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1066 x + ((1 : ℝ) * Sparse.eval nodeValue2040 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((2 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource396 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3385 x + ((2 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((2 : ℝ) * Sparse.eval nodeValue3447 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0))))))))))))))))))))

noncomputable def reducedSource398 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1437 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource399 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource400 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2871 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource401 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource402 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource403 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource404 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((2 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3117 x + 0))))))))))))))))))))

noncomputable def reducedSource405 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource406 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource407 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource408 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((2 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource409 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource410 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((2 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource411 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue5086 x + ((2 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

noncomputable def reducedSource412 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2494 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((2 : ℝ) * Sparse.eval nodeValue2499 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

noncomputable def reducedSource413 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))

noncomputable def reducedSource414 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource415 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource416 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource417 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + 0))))))))))))))))))))

noncomputable def reducedSource418 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

noncomputable def reducedSource419 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((2 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((2 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

noncomputable def reducedSource420 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource421 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue1253 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource422 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource423 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource424 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource425 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1253 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource426 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4437 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue5064 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5071 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource427 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2478 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((2 : ℝ) * Sparse.eval nodeValue2569 x + ((2 : ℝ) * Sparse.eval nodeValue2576 x + ((2 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

noncomputable def reducedSource428 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1643 x + ((2 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((2 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((2 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + 0))))))))))))))))))))

noncomputable def reducedSource429 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource430 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1389 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource431 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1384 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource432 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2857 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2985 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource433 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2985 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource434 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource435 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource436 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource437 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1389 x + ((1 : ℝ) * Sparse.eval nodeValue2857 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource438 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2628 x + ((2 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3106 x + ((2 : ℝ) * Sparse.eval nodeValue3110 x + 0))))))))))))))))))))

noncomputable def reducedSource439 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((2 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource440 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((2 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource441 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2877 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((3 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource442 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2877 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((2 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource443 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource444 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5142 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5193 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))))))))))))))

noncomputable def reducedSource445 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((2 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2853 x + ((2 : ℝ) * Sparse.eval nodeValue2856 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2913 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))))))))))))))

noncomputable def reducedSource446 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue5065 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource447 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2481 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((2 : ℝ) * Sparse.eval nodeValue2572 x + ((2 : ℝ) * Sparse.eval nodeValue2576 x + ((2 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource448 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((2 : ℝ) * Sparse.eval nodeValue3606 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + 0))))))))))))))))))))

noncomputable def reducedSource449 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource450 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource451 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource452 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

noncomputable def reducedSource453 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2746 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((2 : ℝ) * Sparse.eval nodeValue2759 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3003 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3106 x + ((2 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

noncomputable def reducedSource454 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((2 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((2 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

noncomputable def reducedSource455 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((2 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource456 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue997 x + ((2 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1078 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((2 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((2 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

noncomputable def reducedSource457 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1250 x + ((1 : ℝ) * Sparse.eval nodeValue1252 x + ((1 : ℝ) * Sparse.eval nodeValue1253 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource458 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1250 x + ((2 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2746 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource459 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1421 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource460 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource461 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4441 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4443 x + ((2 : ℝ) * Sparse.eval nodeValue4462 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5066 x + ((2 : ℝ) * Sparse.eval nodeValue5077 x + ((2 : ℝ) * Sparse.eval nodeValue5150 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

noncomputable def reducedSource462 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1023 x + ((1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1025 x + ((2 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2472 x + ((2 : ℝ) * Sparse.eval nodeValue2484 x + ((2 : ℝ) * Sparse.eval nodeValue2573 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((2 : ℝ) * Sparse.eval nodeValue2575 x + ((2 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

noncomputable def reducedSource463 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1654 x + ((1 : ℝ) * Sparse.eval nodeValue1655 x + ((2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource464 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource465 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1382 x + ((1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue1390 x + ((2 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource466 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1382 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource467 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2980 x + ((2 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource468 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource469 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1390 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2980 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource470 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3072 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

noncomputable def reducedSource471 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1234 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource472 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2132 x + ((2 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource473 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

noncomputable def reducedSource474 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((2 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2928 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((2 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

noncomputable def reducedSource475 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((2 : ℝ) * Sparse.eval nodeValue3570 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

noncomputable def reducedSource476 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource477 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource478 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1294 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource479 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource48 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2040 x + ((1 : ℝ) * Sparse.eval nodeValue2041 x + ((1 : ℝ) * Sparse.eval nodeValue2042 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource49 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1068 x + ((2 : ℝ) * Sparse.eval nodeValue2042 x + ((2 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

noncomputable def reducedSource50 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((3 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource51 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((1 : ℝ) * Sparse.eval nodeValue1016 x + ((3 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource52 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((3 : ℝ) * Sparse.eval nodeValue2083 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource53 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1457 x + ((3 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource54 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue2010 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource55 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1460 x + ((1 : ℝ) * Sparse.eval nodeValue2083 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource56 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1016 x + ((1 : ℝ) * Sparse.eval nodeValue1457 x + ((3 : ℝ) * Sparse.eval nodeValue1460 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource57 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1078 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((3 : ℝ) * Sparse.eval nodeValue2290 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource58 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue994 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((2 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((2 : ℝ) * Sparse.eval nodeValue2454 x + ((2 : ℝ) * Sparse.eval nodeValue2465 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource59 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3358 x + ((2 : ℝ) * Sparse.eval nodeValue3437 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

noncomputable def reducedSource60 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource61 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue1227 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1279 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource62 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1279 x + ((2 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource63 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1372 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource480 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource481 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue5070 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

noncomputable def reducedSource482 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2477 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2505 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

noncomputable def reducedSource483 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((2 : ℝ) * Sparse.eval nodeValue5249 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5297 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

noncomputable def reducedSource484 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((2 : ℝ) * Sparse.eval nodeValue2708 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((2 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))))))))))

noncomputable def reducedSource485 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((2 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((2 : ℝ) * Sparse.eval nodeValue3066 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3079 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource486 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource487 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4593 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource488 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2917 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2936 x + ((1 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2991 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource489 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource490 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3904 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource491 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource492 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource493 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource494 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource495 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource496 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource497 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5047 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource498 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource499 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((3 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))))))

noncomputable def reducedSource500 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource501 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3211 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource502 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource503 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource504 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2914 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue2988 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3001 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource505 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource506 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource507 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource508 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue2511 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource509 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource510 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource511 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource512 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4996 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource513 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource514 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue5133 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource515 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource516 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2940 x + ((1 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource517 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource518 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((6 : ℝ) * Sparse.eval nodeValue5169 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((3 : ℝ) * Sparse.eval nodeValue5177 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

noncomputable def reducedSource519 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((6 : ℝ) * Sparse.eval nodeValue5168 x + ((3 : ℝ) * Sparse.eval nodeValue5171 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((3 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + ((3 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

noncomputable def reducedSource520 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((6 : ℝ) * Sparse.eval nodeValue5161 x + ((3 : ℝ) * Sparse.eval nodeValue5175 x + ((3 : ℝ) * Sparse.eval nodeValue5272 x + ((3 : ℝ) * Sparse.eval nodeValue5291 x + ((3 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

noncomputable def reducedSource521 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((6 : ℝ) * Sparse.eval nodeValue2964 x + ((3 : ℝ) * Sparse.eval nodeValue2966 x + ((3 : ℝ) * Sparse.eval nodeValue2967 x + ((3 : ℝ) * Sparse.eval nodeValue3103 x + ((3 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))

noncomputable def reducedSource522 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((6 : ℝ) * Sparse.eval nodeValue2719 x + ((3 : ℝ) * Sparse.eval nodeValue2737 x + ((3 : ℝ) * Sparse.eval nodeValue2740 x + ((3 : ℝ) * Sparse.eval nodeValue2761 x + ((3 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

noncomputable def reducedSource523 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4493 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue5094 x + ((6 : ℝ) * Sparse.eval nodeValue5110 x + ((6 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0)))))))

noncomputable def reducedSource524 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5135 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

noncomputable def reducedSource525 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2934 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue2998 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

noncomputable def reducedSource526 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3515 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

noncomputable def reducedSource527 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3908 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource528 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource529 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource530 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource531 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((2 : ℝ) * Sparse.eval nodeValue5014 x + ((2 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((1 : ℝ) * Sparse.eval nodeValue5023 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

noncomputable def reducedSource532 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2385 x + ((2 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((1 : ℝ) * Sparse.eval nodeValue2410 x + ((2 : ℝ) * Sparse.eval nodeValue2462 x + ((2 : ℝ) * Sparse.eval nodeValue2467 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + 0))))))))))))))))))))

noncomputable def reducedSource533 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5242 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

noncomputable def reducedSource534 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2695 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + 0))))))))))))))))))))

noncomputable def reducedSource535 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource536 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0))))))))))))))))))))

noncomputable def reducedSource537 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5241 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))))))))))

noncomputable def reducedSource538 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4600 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5133 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))))))))))

noncomputable def reducedSource539 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((2 : ℝ) * Sparse.eval nodeValue2940 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((2 : ℝ) * Sparse.eval nodeValue2942 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((2 : ℝ) * Sparse.eval nodeValue3003 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((2 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))))))))))

noncomputable def reducedSource540 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2693 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))

noncomputable def reducedSource541 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4421 x + ((2 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4496 x + ((4 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5023 x + ((2 : ℝ) * Sparse.eval nodeValue5055 x + ((4 : ℝ) * Sparse.eval nodeValue5099 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))

noncomputable def reducedSource542 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((2 : ℝ) * Sparse.eval nodeValue4819 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))

noncomputable def reducedSource543 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((2 : ℝ) * Sparse.eval nodeValue2221 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource544 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource545 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4275 x + ((2 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((2 : ℝ) * Sparse.eval nodeValue4746 x + ((4 : ℝ) * Sparse.eval nodeValue4747 x + ((2 : ℝ) * Sparse.eval nodeValue4749 x + ((4 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0)))))))))))))

noncomputable def reducedSource546 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4817 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

noncomputable def reducedSource547 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1443 x + ((2 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((2 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3198 x + ((2 : ℝ) * Sparse.eval nodeValue3211 x + ((2 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))))))))))

noncomputable def reducedSource548 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2207 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + 0))))))))))))))))))))

noncomputable def reducedSource549 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource550 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource551 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4740 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((2 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4750 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0))))))))))))))))))))

noncomputable def reducedSource552 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((2 : ℝ) * Sparse.eval nodeValue1922 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((2 : ℝ) * Sparse.eval nodeValue1929 x + ((2 : ℝ) * Sparse.eval nodeValue1946 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3915 x + 0))))))))))))))))))))

noncomputable def reducedSource553 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

noncomputable def reducedSource554 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + 0))))))))))))))))))))

noncomputable def reducedSource555 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1442 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((2 : ℝ) * Sparse.eval nodeValue3210 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource556 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource557 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4886 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))))

noncomputable def reducedSource558 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((2 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + 0))))))))))))))))))))

noncomputable def reducedSource559 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource560 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource561 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource562 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource563 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource564 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4252 x + ((1 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((2 : ℝ) * Sparse.eval nodeValue4740 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0))))))))))))))))))))

noncomputable def reducedSource565 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((2 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((1 : ℝ) * Sparse.eval nodeValue1900 x + ((2 : ℝ) * Sparse.eval nodeValue1913 x + ((2 : ℝ) * Sparse.eval nodeValue2023 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((2 : ℝ) * Sparse.eval nodeValue2028 x + ((2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + 0))))))))))))))))))))

noncomputable def reducedSource566 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

noncomputable def reducedSource567 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + 0))))))))))))))))))))

noncomputable def reducedSource568 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1366 x + ((2 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((2 : ℝ) * Sparse.eval nodeValue3223 x + ((2 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

noncomputable def reducedSource569 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource570 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

noncomputable def reducedSource571 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((2 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3172 x + ((2 : ℝ) * Sparse.eval nodeValue3174 x + ((2 : ℝ) * Sparse.eval nodeValue3184 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3226 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3228 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

noncomputable def reducedSource572 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + 0))))))))))))))))))))

noncomputable def reducedSource573 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource574 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource575 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource576 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource577 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1020 x + ((2 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource578 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4256 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((2 : ℝ) * Sparse.eval nodeValue4737 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((3 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + 0))))))))))))))))))

noncomputable def reducedSource579 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue1909 x + ((2 : ℝ) * Sparse.eval nodeValue2020 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((2 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3911 x + 0))))))))))))))))))))

noncomputable def reducedSource580 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4455 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

noncomputable def reducedSource581 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + 0))))))))))))))))))))

noncomputable def reducedSource582 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1405 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource583 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource584 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))

noncomputable def reducedSource585 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2227 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))))))))))))))))

noncomputable def reducedSource586 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource587 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))

noncomputable def reducedSource588 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))))))))))

noncomputable def reducedSource589 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4835 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((3 : ℝ) * Sparse.eval nodeValue4846 x + ((3 : ℝ) * Sparse.eval nodeValue4895 x + ((3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

noncomputable def reducedSource590 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((6 : ℝ) * Sparse.eval nodeValue4080 x + ((3 : ℝ) * Sparse.eval nodeValue4081 x + ((3 : ℝ) * Sparse.eval nodeValue4082 x + ((3 : ℝ) * Sparse.eval nodeValue4083 x + ((4 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + 0)))))))))))

noncomputable def reducedSource591 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((2 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2988 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource592 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3527 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + 0))))))))))))))))))))

noncomputable def reducedSource593 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3903 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource594 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((2 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource595 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource596 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource597 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource598 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2614 x + ((2 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource599 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5066 x + ((2 : ℝ) * Sparse.eval nodeValue5077 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5230 x + ((4 : ℝ) * Sparse.eval nodeValue5255 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5262 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))

noncomputable def reducedSource600 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2675 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + 0))))))))))))))))))))

noncomputable def reducedSource601 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2472 x + ((2 : ℝ) * Sparse.eval nodeValue2484 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue3034 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3041 x + ((2 : ℝ) * Sparse.eval nodeValue3084 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

noncomputable def reducedSource602 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource603 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2980 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource604 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2012 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((2 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource605 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource606 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource607 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((2 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource608 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((2 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + 0))))))))))))))))))))

noncomputable def reducedSource609 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3906 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

noncomputable def reducedSource610 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1276 x + ((1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource611 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2493 x + ((2 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource612 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4406 x + ((2 : ℝ) * Sparse.eval nodeValue4407 x + ((1 : ℝ) * Sparse.eval nodeValue4414 x + ((1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue5004 x + ((2 : ℝ) * Sparse.eval nodeValue5005 x + ((1 : ℝ) * Sparse.eval nodeValue5011 x + ((2 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((2 : ℝ) * Sparse.eval nodeValue5243 x + ((2 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + 0))))))))))))))))))))

noncomputable def reducedSource613 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((2 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue2389 x + ((2 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2636 x + ((2 : ℝ) * Sparse.eval nodeValue2697 x + ((2 : ℝ) * Sparse.eval nodeValue2698 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

noncomputable def reducedSource614 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1593 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue2912 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3337 x + ((2 : ℝ) * Sparse.eval nodeValue3342 x + ((2 : ℝ) * Sparse.eval nodeValue3488 x + ((2 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((2 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

noncomputable def reducedSource615 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource616 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1360 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue1421 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource617 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource618 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource619 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((2 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource620 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4794 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4806 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5230 x + ((3 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5262 x + ((2 : ℝ) * Sparse.eval nodeValue5263 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))

noncomputable def reducedSource621 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2117 x + ((2 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2675 x + ((2 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2727 x + ((2 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3093 x + 0))))))))))))))))))))

noncomputable def reducedSource622 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2024 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue3034 x + ((2 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3041 x + ((2 : ℝ) * Sparse.eval nodeValue3043 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3203 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

noncomputable def reducedSource623 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource624 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3150 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((3 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource625 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((2 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3150 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource626 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((2 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource627 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource628 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue5166 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + ((4 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + 0)))))))))))))

noncomputable def reducedSource629 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1293 x + ((2 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue2953 x + ((4 : ℝ) * Sparse.eval nodeValue2954 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((2 : ℝ) * Sparse.eval nodeValue3053 x + ((2 : ℝ) * Sparse.eval nodeValue3054 x + ((4 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((2 : ℝ) * Sparse.eval nodeValue4012 x + ((2 : ℝ) * Sparse.eval nodeValue4019 x + 0)))))))))))))

noncomputable def reducedSource630 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((4 : ℝ) * Sparse.eval nodeValue5102 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

noncomputable def reducedSource631 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2508 x + ((2 : ℝ) * Sparse.eval nodeValue2509 x + ((4 : ℝ) * Sparse.eval nodeValue2512 x + ((4 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue3984 x + ((2 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0)))))))))))))

noncomputable def reducedSource632 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((4 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((4 : ℝ) * Sparse.eval nodeValue5304 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))

noncomputable def reducedSource633 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((2 : ℝ) * Sparse.eval nodeValue3085 x + ((4 : ℝ) * Sparse.eval nodeValue3097 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((4 : ℝ) * Sparse.eval nodeValue3109 x + ((2 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

noncomputable def reducedSource634 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3581 x + ((2 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((1 : ℝ) * Sparse.eval nodeValue3628 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource635 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource636 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2506 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource637 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource638 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource639 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

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

noncomputable def reducedSource64 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource65 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource66 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((2 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource67 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1424 x + ((2 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource68 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1227 x + ((2 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1424 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource69 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2065 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource70 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource72 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3160 x + ((2 : ℝ) * Sparse.eval nodeValue3393 x + ((2 : ℝ) * Sparse.eval nodeValue3396 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource73 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue3393 x + ((1 : ℝ) * Sparse.eval nodeValue3495 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource74 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3154 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3495 x + ((2 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource75 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2063 x + ((2 : ℝ) * Sparse.eval nodeValue3154 x + ((1 : ℝ) * Sparse.eval nodeValue3160 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource77 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource640 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource641 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource642 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4449 x + ((1 : ℝ) * Sparse.eval nodeValue4450 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4487 x + ((1 : ℝ) * Sparse.eval nodeValue5069 x + ((1 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5092 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource643 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2476 x + ((1 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2501 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource644 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1641 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3442 x + ((1 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource645 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource646 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1403 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource647 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource648 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource649 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2583 x + ((1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2717 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2749 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2762 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2772 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource650 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource651 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource652 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource653 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue2962 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource654 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource655 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2995 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource656 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + 0)))))))))))))))))))

noncomputable def reducedSource657 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1235 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + ((2 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))))))))

noncomputable def reducedSource658 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

noncomputable def reducedSource659 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1039 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

noncomputable def reducedSource660 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))

noncomputable def reducedSource661 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((1 : ℝ) * Sparse.eval nodeValue3628 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource662 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3618 x + ((2 : ℝ) * Sparse.eval nodeValue3622 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource663 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource664 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2465 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource665 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1276 x + ((1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue1278 x + ((1 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource666 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4469 x + ((1 : ℝ) * Sparse.eval nodeValue4470 x + ((1 : ℝ) * Sparse.eval nodeValue4471 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue5082 x + ((1 : ℝ) * Sparse.eval nodeValue5083 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5091 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource667 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource668 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1638 x + ((1 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3441 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource669 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource670 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1364 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource671 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1364 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource672 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue2977 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource673 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource674 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource675 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((1 : ℝ) * Sparse.eval nodeValue2132 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2756 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2772 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3116 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource676 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource677 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue3551 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource678 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2929 x + ((1 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3152 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource679 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue2929 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource680 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource681 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3152 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3551 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource682 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4473 x + ((3 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4494 x + ((3 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((3 : ℝ) * Sparse.eval nodeValue5203 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((6 : ℝ) * Sparse.eval nodeValue5266 x + ((3 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))

noncomputable def reducedSource683 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((3 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((3 : ℝ) * Sparse.eval nodeValue3075 x + ((3 : ℝ) * Sparse.eval nodeValue3461 x + ((3 : ℝ) * Sparse.eval nodeValue3526 x + ((6 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((3 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))

noncomputable def reducedSource684 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((3 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource685 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2746 x + ((3 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource686 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4878 x + ((3 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4886 x + ((3 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5286 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((6 : ℝ) * Sparse.eval nodeValue5299 x + 0))))))))))))

noncomputable def reducedSource687 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((3 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((3 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue3023 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((6 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource688 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2457 x + ((2 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((2 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

noncomputable def reducedSource689 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource690 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue1248 x + ((1 : ℝ) * Sparse.eval nodeValue1250 x + ((2 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource691 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource692 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource693 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4449 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource694 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((2 : ℝ) * Sparse.eval nodeValue1032 x + ((2 : ℝ) * Sparse.eval nodeValue2566 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((2 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

noncomputable def reducedSource695 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1635 x + ((2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((2 : ℝ) * Sparse.eval nodeValue3558 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + 0))))))))))))))))))))

noncomputable def reducedSource696 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource697 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1387 x + ((2 : ℝ) * Sparse.eval nodeValue1403 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource698 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource699 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource700 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((2 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2583 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2749 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2752 x + ((2 : ℝ) * Sparse.eval nodeValue2756 x + ((2 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3104 x + ((1 : ℝ) * Sparse.eval nodeValue3105 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + 0)))))))))))))))))))

noncomputable def reducedSource701 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3489 x + ((1 : ℝ) * Sparse.eval nodeValue3496 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource702 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource703 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2923 x + ((2 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource704 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource705 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3489 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((2 : ℝ) * Sparse.eval nodeValue3551 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource706 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4581 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5202 x + ((6 : ℝ) * Sparse.eval nodeValue5284 x + ((6 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5452 x + 0)))))))

noncomputable def reducedSource707 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1235 x + ((6 : ℝ) * Sparse.eval nodeValue2853 x + ((2 : ℝ) * Sparse.eval nodeValue2880 x + ((6 : ℝ) * Sparse.eval nodeValue3077 x + ((6 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))

noncomputable def reducedSource708 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue4887 x + ((3 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5273 x + ((6 : ℝ) * Sparse.eval nodeValue5281 x + ((6 : ℝ) * Sparse.eval nodeValue5286 x + ((6 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + 0)))))))

noncomputable def reducedSource709 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2741 x + ((6 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3053 x + ((6 : ℝ) * Sparse.eval nodeValue3074 x + ((6 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3226 x + 0)))))))

noncomputable def reducedSource710 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4600 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0))))))))))))))))))))

noncomputable def reducedSource711 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((2 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2957 x + ((2 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))

noncomputable def reducedSource712 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((2 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

noncomputable def reducedSource713 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3904 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource714 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource715 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1293 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource716 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2631 x + ((2 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource717 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

noncomputable def reducedSource718 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((2 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

noncomputable def reducedSource719 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))))))

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

noncomputable def reducedSource720 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

noncomputable def reducedSource721 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4589 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((2 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))

noncomputable def reducedSource722 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((2 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2986 x + ((2 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2999 x + ((2 : ℝ) * Sparse.eval nodeValue3064 x + ((2 : ℝ) * Sparse.eval nodeValue3065 x + ((2 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((2 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4038 x + 0))))))))))))))))))))

noncomputable def reducedSource723 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3469 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((2 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + 0))))))))))))))))))))

noncomputable def reducedSource724 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue2510 x + ((3 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource725 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource726 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4996 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

noncomputable def reducedSource727 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((2 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + 0))))))))))))))))))))

noncomputable def reducedSource728 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((3 : ℝ) * Sparse.eval nodeValue5256 x + ((4 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))

noncomputable def reducedSource729 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + 0))))))))))))))))))))

noncomputable def reducedSource730 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5160 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

noncomputable def reducedSource731 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2951 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((2 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

noncomputable def reducedSource732 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3558 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


