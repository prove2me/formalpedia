-- Prove2me | Definitions.Def_OAIQ106E129
-- name    : OAIQ106E129
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:12:00.587876+00:00
-- url     : https://prove2.me/theorems/a3f3511a-90f2-4411-83ce-8b9f3e363db7
-- title:
--   Definitions bundle OAIQ106E129 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 54 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource948`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource949`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource950`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource951`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource952`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource953`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource955`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource956`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource957`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource958`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource959`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource96`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource960`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource961`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource962`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource963`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource964`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource965`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource966`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource967`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource968`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource969`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource97`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource970`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource971`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource972`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource973`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource974`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource975`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource976`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource977`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource978`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource979`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource98`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource980`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource981`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource982`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource983`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource984`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource985` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSources_Arithmetic59`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Arithmetic59.lean), [`MutuallyUnbiased_MixedSources_Arithmetic6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Arithmetic6.lean), [`MutuallyUnbiased_MixedSources_Arithmetic60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Arithmetic60.lean), [`MutuallyUnbiased_MixedSources_Arithmetic61`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Arithmetic61.lean), [`MutuallyUnbiased_MixedSources_Arithmetic62`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Arithmetic62.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource948 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource949 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4090 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + ((1 : ℝ) * Sparse.eval nodeValue4096 x + 0)))))))))))

noncomputable def reducedSource950 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5166 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))))))))

noncomputable def reducedSource951 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

noncomputable def reducedSource952 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))

noncomputable def reducedSource953 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

noncomputable def reducedSource955 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4815 x + ((1 : ℝ) * Sparse.eval nodeValue4830 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((3 : ℝ) * Sparse.eval nodeValue5359 x + ((3 : ℝ) * Sparse.eval nodeValue5406 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((6 : ℝ) * Sparse.eval nodeValue5425 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + 0)))))))))))

noncomputable def reducedSource956 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4864 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

noncomputable def reducedSource957 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

noncomputable def reducedSource958 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue5123 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5192 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5391 x + ((6 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((3 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))

noncomputable def reducedSource959 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2853 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3370 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((3 : ℝ) * Sparse.eval nodeValue3778 x + ((6 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue4007 x + ((3 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + ((3 : ℝ) * Sparse.eval nodeValue4039 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource96 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource97 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((1 : ℝ) * Sparse.eval nodeValue4285 x + ((3 : ℝ) * Sparse.eval nodeValue4572 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((6 : ℝ) * Sparse.eval nodeValue4747 x + ((3 : ℝ) * Sparse.eval nodeValue4754 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((3 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))

noncomputable def reducedSource98 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue860 x + ((3 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((6 : ℝ) * Sparse.eval nodeValue1926 x + ((3 : ℝ) * Sparse.eval nodeValue1951 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((3 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((3 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + 0))))))))))))

noncomputable def reducedSource99 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4476 x + ((3 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4481 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((6 : ℝ) * Sparse.eval nodeValue4817 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((3 : ℝ) * Sparse.eval nodeValue4881 x + ((3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((3 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource960 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((3 : ℝ) * Sparse.eval nodeValue5406 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((6 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))

noncomputable def reducedSource961 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((3 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5359 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((6 : ℝ) * Sparse.eval nodeValue5445 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((3 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + 0))))))))))))

noncomputable def reducedSource962 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((3 : ℝ) * Sparse.eval nodeValue3074 x + ((3 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((3 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((3 : ℝ) * Sparse.eval nodeValue3952 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3975 x + ((6 : ℝ) * Sparse.eval nodeValue4024 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + ((3 : ℝ) * Sparse.eval nodeValue4033 x + 0))))))))))))

noncomputable def reducedSource963 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

noncomputable def reducedSource964 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))))

noncomputable def reducedSource965 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5069 x + ((1 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5092 x + ((1 : ℝ) * Sparse.eval nodeValue5132 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5350 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5362 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource966 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue3442 x + ((1 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource967 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2476 x + ((1 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2501 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3499 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3700 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3966 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource968 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))

noncomputable def reducedSource969 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))))

noncomputable def reducedSource970 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

noncomputable def reducedSource971 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue3687 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3701 x + ((2 : ℝ) * Sparse.eval nodeValue3787 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4011 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

noncomputable def reducedSource972 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

noncomputable def reducedSource973 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

noncomputable def reducedSource974 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))

noncomputable def reducedSource975 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource976 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5094 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))

noncomputable def reducedSource977 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))

noncomputable def reducedSource978 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5055 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5344 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0)))))))))))))))))

noncomputable def reducedSource979 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue5396 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((6 : ℝ) * Sparse.eval nodeValue5478 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((3 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))

noncomputable def reducedSource980 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))))))))

noncomputable def reducedSource981 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((2 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

noncomputable def reducedSource982 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4996 x + ((2 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5013 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((4 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5469 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))

noncomputable def reducedSource983 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4859 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue5383 x + ((4 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5398 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))

noncomputable def reducedSource984 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource985 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((2 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

noncomputable def reducedSource986 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

noncomputable def reducedSource987 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3735 x + ((2 : ℝ) * Sparse.eval nodeValue3749 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((2 : ℝ) * Sparse.eval nodeValue3799 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3897 x + ((2 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + 0))))))))))))))))))))

noncomputable def reducedSource988 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0)))))))))))))))))))

noncomputable def reducedSource989 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

noncomputable def reducedSource990 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((3 : ℝ) * Sparse.eval nodeValue5396 x + ((6 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + ((3 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))

noncomputable def reducedSource991 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4079 x + ((3 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((3 : ℝ) * Sparse.eval nodeValue4088 x + ((3 : ℝ) * Sparse.eval nodeValue4090 x + ((5 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((3 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4095 x + ((3 : ℝ) * Sparse.eval nodeValue4096 x + 0))))))))))

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

noncomputable def reducedSource993 (x : Master → ℝ) : ℝ :=
  (9 : ℝ) * Sparse.eval nodeValue4090 x + ((12 : ℝ) * Sparse.eval nodeValue4091 x + ((9 : ℝ) * Sparse.eval nodeValue4096 x + 0))

noncomputable def reducedSource994 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue617 x + ((3 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource995 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue862 x + ((3 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

noncomputable def reducedSource996 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

noncomputable def reducedSource997 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue587 x + ((2 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue951 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource998 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue849 x + ((2 : ℝ) * Sparse.eval nodeValue1615 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1752 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

noncomputable def reducedSource999 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue794 x + ((1 : ℝ) * Sparse.eval nodeValue797 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


