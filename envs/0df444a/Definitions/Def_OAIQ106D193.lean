-- Prove2me | Definitions.Def_OAIQ106D193
-- name    : OAIQ106D193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:01:28.595198+00:00
-- url     : https://prove2.me/theorems/fe22990b-c60b-4da7-a703-8b89599ae3f1
-- title:
--   Definitions bundle OAIQ106D193 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 310 declarations of OpenAI's Lean: 310 definitions. The definitions and types are `OAI.MUB6.TaoCertificate.combined476_part8`, `OAI.MUB6.TaoCertificate.combined476_part9`, `OAI.MUB6.TaoCertificate.combined477`, `OAI.MUB6.TaoCertificate.combined477_part0`, `OAI.MUB6.TaoCertificate.combined477_part1`, `OAI.MUB6.TaoCertificate.combined477_part10`, `OAI.MUB6.TaoCertificate.combined477_part11`, `OAI.MUB6.TaoCertificate.combined477_part12`, `OAI.MUB6.TaoCertificate.combined477_part13`, `OAI.MUB6.TaoCertificate.combined477_part2`, `OAI.MUB6.TaoCertificate.combined477_part3`, `OAI.MUB6.TaoCertificate.combined477_part4`, `OAI.MUB6.TaoCertificate.combined477_part5`, `OAI.MUB6.TaoCertificate.combined477_part6`, `OAI.MUB6.TaoCertificate.combined477_part7`, `OAI.MUB6.TaoCertificate.combined477_part8`, `OAI.MUB6.TaoCertificate.combined477_part9`, `OAI.MUB6.TaoCertificate.combined478`, `OAI.MUB6.TaoCertificate.combined478_part0`, `OAI.MUB6.TaoCertificate.combined478_part1`, `OAI.MUB6.TaoCertificate.combined478_part10`, `OAI.MUB6.TaoCertificate.combined478_part11`, `OAI.MUB6.TaoCertificate.combined478_part12`, `OAI.MUB6.TaoCertificate.combined478_part13`, `OAI.MUB6.TaoCertificate.combined478_part2`, `OAI.MUB6.TaoCertificate.combined478_part3`, `OAI.MUB6.TaoCertificate.combined478_part4`, `OAI.MUB6.TaoCertificate.combined478_part5`, `OAI.MUB6.TaoCertificate.combined478_part6`, `OAI.MUB6.TaoCertificate.combined478_part7`, `OAI.MUB6.TaoCertificate.combined478_part8`, `OAI.MUB6.TaoCertificate.combined478_part9`, `OAI.MUB6.TaoCertificate.combined48`, `OAI.MUB6.TaoCertificate.combined48_part0`, `OAI.MUB6.TaoCertificate.combined48_part1`, `OAI.MUB6.TaoCertificate.combined49`, `OAI.MUB6.TaoCertificate.combined49_part0`, `OAI.MUB6.TaoCertificate.combined49_part1`, `OAI.MUB6.TaoCertificate.combined5`, `OAI.MUB6.TaoCertificate.combined50` and 270 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_TaoCertificate_CubeTarget`, `MutuallyUnbiased_TaoCertificate_KnownTarget0`, `MutuallyUnbiased_TaoCertificate_KnownTarget1`, `MutuallyUnbiased_TaoCertificate_KnownTarget10`, `MutuallyUnbiased_TaoCertificate_KnownTarget11`, `MutuallyUnbiased_TaoCertificate_KnownTarget12`, `MutuallyUnbiased_TaoCertificate_KnownTarget13`, `MutuallyUnbiased_TaoCertificate_KnownTarget2`, `MutuallyUnbiased_TaoCertificate_KnownTarget3`, `MutuallyUnbiased_TaoCertificate_KnownTarget4`, `MutuallyUnbiased_TaoCertificate_KnownTarget5`, `MutuallyUnbiased_TaoCertificate_KnownTarget6`, `MutuallyUnbiased_TaoCertificate_KnownTarget7`, `MutuallyUnbiased_TaoCertificate_KnownTarget8`, `MutuallyUnbiased_TaoCertificate_KnownTarget9`, `MutuallyUnbiased_TaoCertificate_Merge0`, `MutuallyUnbiased_TaoCertificate_Merge1`, `MutuallyUnbiased_TaoCertificate_Merge10`, `MutuallyUnbiased_TaoCertificate_Merge11`, `MutuallyUnbiased_TaoCertificate_Merge12`, `MutuallyUnbiased_TaoCertificate_Merge59`, `MutuallyUnbiased_TaoCertificate_Merge6`, `MutuallyUnbiased_TaoCertificate_Merge7`, `MutuallyUnbiased_TaoCertificate_Merge8`, `MutuallyUnbiased_TaoCertificate_Merge9`, `MutuallyUnbiased_TaoCertificate_Rows0`, `MutuallyUnbiased_TaoCertificate_Rows1`, `MutuallyUnbiased_TaoCertificate_Rows12`, `MutuallyUnbiased_TaoCertificate_Rows13`, `MutuallyUnbiased_TaoCertificate_Rows14`, `MutuallyUnbiased_TaoCertificate_Rows15`, `MutuallyUnbiased_TaoCertificate_Rows16`, `MutuallyUnbiased_TaoCertificate_Rows17`, `MutuallyUnbiased_TaoCertificate_Rows18`, `MutuallyUnbiased_TaoCertificate_Rows19`, `MutuallyUnbiased_TaoCertificate_Rows2`, `MutuallyUnbiased_TaoCertificate_Rows20`, `MutuallyUnbiased_TaoCertificate_Rows21`, `MutuallyUnbiased_TaoCertificate_TargetMerge1`, `MutuallyUnbiased_TaoCertificate_TargetMerge10`, `MutuallyUnbiased_Tao_TaoFamily`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_CubeTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def cubeTarget : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -3, 0, 3, 0, 0], 36), ([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 0, 3, 0, -3, 0], 36), ([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 0, 3, 0, -3, 0, 0], 36), ([0, 0, 3, 0, 0, -3, 0], 36), ([0, 0, 3, 0, 0, 0, -3], 36), ([0, 3, -3, 0, 0, 0, 0], 36), ([0, 3, 0, -3, 0, 0, 0], 36), ([0, 3, 0, 0, -3, 0, 0], 36), ([0, 3, 0, 0, 0, -3, 0], 36), ([0, 3, 0, 0, 0, 0, -3], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams0 : List (Charge × Coeff) := [(![-2, 0, 0, 0, 1, 1], (0, -36)), (![-2, 0, 0, 1, 0, 1], (36, 36)), (![-2, 0, 0, 1, 1, 0], (0, -36)), (![-2, 0, 1, 0, 0, 1], (36, 36)), (![-2, 0, 1, 0, 1, 0], (36, 36)), (![-2, 0, 1, 1, 0, 0], (0, -36)), (![-2, 1, 0, 0, 0, 1], (0, -36)), (![-2, 1, 0, 0, 1, 0], (36, 36)), (![-2, 1, 0, 1, 0, 0], (36, 36)), (![-2, 1, 1, 0, 0, 0], (0, -36)), (![-1, -1, 0, 0, 0, 2], (36, 36)), (![-1, -1, 0, 0, 2, 0], (0, -36)), (![-1, -1, 0, 2, 0, 0], (0, -36)), (![-1, -1, 2, 0, 0, 0], (36, 36)), (![-1, 0, -1, 0, 0, 2], (0, -36))]

def knownTarget0 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 2, 0, 0, 0], 36), ([1, -2, 0, 0, 0, 1, 1], -36), ([1, -2, 0, 0, 1, 0, 1], 36), ([1, -2, 0, 0, 1, 1, 0], -36), ([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams1 : List (Charge × Coeff) := [(![-1, 0, -1, 0, 2, 0], (0, -36)), (![-1, 0, -1, 2, 0, 0], (36, 36)), (![-1, 0, 0, -1, 0, 2], (0, -36)), (![-1, 0, 0, -1, 2, 0], (36, 36)), (![-1, 0, 0, 0, -1, 2], (36, 36)), (![-1, 0, 0, 0, 2, -1], (36, 36)), (![-1, 0, 0, 2, -1, 0], (36, 36)), (![-1, 0, 0, 2, 0, -1], (0, -36)), (![-1, 0, 2, -1, 0, 0], (36, 36)), (![-1, 0, 2, 0, -1, 0], (0, -36)), (![-1, 0, 2, 0, 0, -1], (0, -36)), (![-1, 2, -1, 0, 0, 0], (36, 36)), (![-1, 2, 0, -1, 0, 0], (0, -36)), (![-1, 2, 0, 0, -1, 0], (0, -36)), (![-1, 2, 0, 0, 0, -1], (36, 36))]

def knownTarget1 : Sparse := [([0, -1, 0, -1, 2, 0, 0], 36), ([0, -1, 0, 0, -1, 2, 0], 36), ([0, -1, 0, 0, 0, -1, 2], 36), ([0, -1, 0, 0, 0, 2, -1], 36), ([0, -1, 0, 0, 2, -1, 0], 36), ([0, -1, 0, 2, -1, 0, 0], 36), ([0, -1, 2, -1, 0, 0, 0], 36), ([0, -1, 2, 0, 0, 0, -1], 36), ([1, -1, 0, -1, 0, 2, 0], -36), ([1, -1, 0, -1, 2, 0, 0], 36), ([1, -1, 0, 0, -1, 0, 2], -36), ([1, -1, 0, 0, -1, 2, 0], 36), ([1, -1, 0, 0, 0, -1, 2], 36), ([1, -1, 0, 0, 0, 2, -1], 36), ([1, -1, 0, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 2, 0, -1], -36), ([1, -1, 0, 2, -1, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], -36), ([1, -1, 0, 2, 0, 0, -1], -36), ([1, -1, 2, -1, 0, 0, 0], 36), ([1, -1, 2, 0, -1, 0, 0], -36), ([1, -1, 2, 0, 0, -1, 0], -36), ([1, -1, 2, 0, 0, 0, -1], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams10 : List (Charge × Coeff) := [(![0, -1, -1, 0, 1, 1], (-144, 0)), (![0, -1, -1, 1, 0, 1], (0, -144)), (![0, -1, -1, 1, 1, 0], (-144, 0)), (![0, -1, 0, -1, 1, 1], (144, 144)), (![0, -1, 0, 1, -1, 1], (-144, 0)), (![0, -1, 0, 1, 1, -1], (-144, 0)), (![0, -1, 1, -1, 0, 1], (-144, 0)), (![0, -1, 1, -1, 1, 0], (-144, 0)), (![0, -1, 1, 0, -1, 1], (-144, 0)), (![0, -1, 1, 0, 1, -1], (0, -144)), (![0, -1, 1, 1, -1, 0], (144, 144)), (![0, -1, 1, 1, 0, -1], (-144, 0)), (![0, 0, -1, -1, 1, 1], (-144, 0)), (![0, 0, -1, 1, -1, 1], (-144, 0)), (![0, 0, -1, 1, 1, -1], (144, 144))]

def knownTarget10 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -144), ([0, 0, -1, -1, 1, 1, 0], -144), ([0, 0, -1, 0, -1, 1, 1], 144), ([0, 0, -1, 0, 1, -1, 1], -144), ([0, 0, -1, 0, 1, 1, -1], -144), ([0, 0, -1, 1, -1, 0, 1], -144), ([0, 0, -1, 1, -1, 1, 0], -144), ([0, 0, -1, 1, 0, -1, 1], -144), ([0, 0, -1, 1, 1, -1, 0], 144), ([0, 0, -1, 1, 1, 0, -1], -144), ([0, 0, 0, -1, -1, 1, 1], -144), ([0, 0, 0, -1, 1, -1, 1], -144), ([0, 0, 0, -1, 1, 1, -1], 144), ([1, 0, -1, -1, 1, 0, 1], -144), ([1, 0, -1, 0, -1, 1, 1], 144), ([1, 0, -1, 1, 0, 1, -1], -144), ([1, 0, -1, 1, 1, -1, 0], 144), ([1, 0, 0, -1, 1, 1, -1], 144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams11 : List (Charge × Coeff) := [(![0, 0, 1, -1, -1, 1], (0, -144)), (![0, 0, 1, -1, 1, -1], (-144, 0)), (![0, 0, 1, 1, -1, -1], (-144, 0)), (![0, 1, -1, -1, 0, 1], (-144, 0)), (![0, 1, -1, -1, 1, 0], (0, -144)), (![0, 1, -1, 0, -1, 1], (144, 144)), (![0, 1, -1, 0, 1, -1], (-144, 0)), (![0, 1, -1, 1, -1, 0], (-144, 0)), (![0, 1, -1, 1, 0, -1], (-144, 0)), (![0, 1, 0, -1, -1, 1], (-144, 0)), (![0, 1, 0, -1, 1, -1], (-144, 0)), (![0, 1, 0, 1, -1, -1], (0, -144)), (![0, 1, 1, -1, -1, 0], (-144, 0)), (![0, 1, 1, -1, 0, -1], (144, 144)), (![0, 1, 1, 0, -1, -1], (-144, 0))]

def knownTarget11 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -144), ([0, 0, 0, 1, 1, -1, -1], -144), ([0, 0, 1, -1, -1, 0, 1], -144), ([0, 0, 1, -1, 0, -1, 1], 144), ([0, 0, 1, -1, 0, 1, -1], -144), ([0, 0, 1, -1, 1, -1, 0], -144), ([0, 0, 1, -1, 1, 0, -1], -144), ([0, 0, 1, 0, -1, -1, 1], -144), ([0, 0, 1, 0, -1, 1, -1], -144), ([0, 0, 1, 1, -1, -1, 0], -144), ([0, 0, 1, 1, -1, 0, -1], 144), ([0, 0, 1, 1, 0, -1, -1], -144), ([1, 0, 0, 1, -1, -1, 1], -144), ([1, 0, 1, -1, -1, 1, 0], -144), ([1, 0, 1, -1, 0, -1, 1], 144), ([1, 0, 1, 0, 1, -1, -1], -144), ([1, 0, 1, 1, -1, 0, -1], 144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams12 : List (Charge × Coeff) := [(![1, -1, -1, 0, 0, 1], (-144, 0)), (![1, -1, -1, 0, 1, 0], (144, 144)), (![1, -1, -1, 1, 0, 0], (-144, 0)), (![1, -1, 0, -1, 0, 1], (-144, 0)), (![1, -1, 0, -1, 1, 0], (-144, 0)), (![1, -1, 0, 0, -1, 1], (0, -144)), (![1, -1, 0, 0, 1, -1], (-144, 0)), (![1, -1, 0, 1, -1, 0], (-144, 0)), (![1, -1, 0, 1, 0, -1], (144, 144)), (![1, -1, 1, -1, 0, 0], (0, -144)), (![1, -1, 1, 0, -1, 0], (-144, 0)), (![1, -1, 1, 0, 0, -1], (-144, 0)), (![1, 0, -1, -1, 0, 1], (144, 144)), (![1, 0, -1, -1, 1, 0], (-144, 0)), (![1, 0, -1, 0, -1, 1], (-144, 0))]

def knownTarget12 : Sparse := [([0, 1, -1, -1, 0, 0, 1], -144), ([0, 1, -1, -1, 0, 1, 0], 144), ([0, 1, -1, -1, 1, 0, 0], -144), ([0, 1, -1, 0, -1, 0, 1], -144), ([0, 1, -1, 0, -1, 1, 0], -144), ([0, 1, -1, 0, 0, 1, -1], -144), ([0, 1, -1, 0, 1, -1, 0], -144), ([0, 1, -1, 0, 1, 0, -1], 144), ([0, 1, -1, 1, 0, -1, 0], -144), ([0, 1, -1, 1, 0, 0, -1], -144), ([0, 1, 0, -1, -1, 0, 1], 144), ([0, 1, 0, -1, -1, 1, 0], -144), ([0, 1, 0, -1, 0, -1, 1], -144), ([1, 1, -1, -1, 0, 1, 0], 144), ([1, 1, -1, 0, 0, -1, 1], -144), ([1, 1, -1, 0, 1, 0, -1], 144), ([1, 1, -1, 1, -1, 0, 0], -144), ([1, 1, 0, -1, -1, 0, 1], 144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams13 : List (Charge × Coeff) := [(![1, 0, -1, 0, 1, -1], (-144, 0)), (![1, 0, -1, 1, -1, 0], (0, -144)), (![1, 0, -1, 1, 0, -1], (-144, 0)), (![1, 0, 0, -1, -1, 1], (-144, 0)), (![1, 0, 0, -1, 1, -1], (0, -144)), (![1, 0, 0, 1, -1, -1], (-144, 0)), (![1, 0, 1, -1, -1, 0], (-144, 0)), (![1, 0, 1, -1, 0, -1], (-144, 0)), (![1, 0, 1, 0, -1, -1], (144, 144)), (![1, 1, -1, -1, 0, 0], (-144, 0)), (![1, 1, -1, 0, -1, 0], (-144, 0)), (![1, 1, -1, 0, 0, -1], (0, -144)), (![1, 1, 0, -1, -1, 0], (144, 144)), (![1, 1, 0, -1, 0, -1], (-144, 0)), (![1, 1, 0, 0, -1, -1], (-144, 0))]

def knownTarget13 : Sparse := [([0, 1, 0, -1, 0, 1, -1], -144), ([0, 1, 0, -1, 1, 0, -1], -144), ([0, 1, 0, 0, -1, -1, 1], -144), ([0, 1, 0, 0, 1, -1, -1], -144), ([0, 1, 0, 1, -1, -1, 0], -144), ([0, 1, 0, 1, -1, 0, -1], -144), ([0, 1, 0, 1, 0, -1, -1], 144), ([0, 1, 1, -1, -1, 0, 0], -144), ([0, 1, 1, -1, 0, -1, 0], -144), ([0, 1, 1, 0, -1, -1, 0], 144), ([0, 1, 1, 0, -1, 0, -1], -144), ([0, 1, 1, 0, 0, -1, -1], -144), ([1, 1, 0, -1, 1, -1, 0], -144), ([1, 1, 0, 0, -1, 1, -1], -144), ([1, 1, 0, 1, 0, -1, -1], 144), ([1, 1, 1, -1, 0, 0, -1], -144), ([1, 1, 1, 0, -1, -1, 0], 144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams2 : List (Charge × Coeff) := [(![0, -2, 0, 0, 1, 1], (36, 36)), (![0, -2, 0, 1, 0, 1], (0, -36)), (![0, -2, 0, 1, 1, 0], (0, -36)), (![0, -2, 1, 0, 0, 1], (36, 36)), (![0, -2, 1, 0, 1, 0], (0, -36)), (![0, -2, 1, 1, 0, 0], (36, 36)), (![0, -1, -1, 0, 0, 2], (0, -36)), (![0, -1, -1, 0, 2, 0], (36, 36)), (![0, -1, -1, 2, 0, 0], (0, -36)), (![0, -1, 0, -1, 0, 2], (36, 36)), (![0, -1, 0, -1, 2, 0], (36, 36)), (![0, -1, 0, 0, -1, 2], (0, -36)), (![0, -1, 0, 0, 2, -1], (0, -36)), (![0, -1, 0, 2, -1, 0], (36, 36)), (![0, -1, 0, 2, 0, -1], (36, 36))]

def knownTarget2 : Sparse := [([0, 0, -2, 0, 0, 1, 1], 36), ([0, 0, -2, 1, 0, 0, 1], 36), ([0, 0, -2, 1, 1, 0, 0], 36), ([0, 0, -1, -1, 0, 2, 0], 36), ([0, 0, -1, 0, -1, 0, 2], 36), ([0, 0, -1, 0, -1, 2, 0], 36), ([0, 0, -1, 0, 2, -1, 0], 36), ([0, 0, -1, 0, 2, 0, -1], 36), ([1, 0, -2, 0, 0, 1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], -36), ([1, 0, -2, 0, 1, 1, 0], -36), ([1, 0, -2, 1, 0, 0, 1], 36), ([1, 0, -2, 1, 0, 1, 0], -36), ([1, 0, -2, 1, 1, 0, 0], 36), ([1, 0, -1, -1, 0, 0, 2], -36), ([1, 0, -1, -1, 0, 2, 0], 36), ([1, 0, -1, -1, 2, 0, 0], -36), ([1, 0, -1, 0, -1, 0, 2], 36), ([1, 0, -1, 0, -1, 2, 0], 36), ([1, 0, -1, 0, 0, -1, 2], -36), ([1, 0, -1, 0, 0, 2, -1], -36), ([1, 0, -1, 0, 2, -1, 0], 36), ([1, 0, -1, 0, 2, 0, -1], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams3 : List (Charge × Coeff) := [(![0, -1, 2, -1, 0, 0], (0, -36)), (![0, -1, 2, 0, -1, 0], (36, 36)), (![0, -1, 2, 0, 0, -1], (0, -36)), (![0, 0, -2, 0, 1, 1], (0, -36)), (![0, 0, -2, 1, 0, 1], (0, -36)), (![0, 0, -2, 1, 1, 0], (36, 36)), (![0, 0, -1, -1, 0, 2], (36, 36)), (![0, 0, -1, -1, 2, 0], (0, -36)), (![0, 0, -1, 0, -1, 2], (36, 36)), (![0, 0, -1, 0, 2, -1], (36, 36)), (![0, 0, -1, 2, -1, 0], (0, -36)), (![0, 0, -1, 2, 0, -1], (36, 36)), (![0, 0, 0, -2, 1, 1], (36, 36)), (![0, 0, 0, -1, -1, 2], (0, -36)), (![0, 0, 0, -1, 2, -1], (0, -36))]

def knownTarget3 : Sparse := [([0, 0, -1, 2, 0, -1, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 36), ([0, 0, 0, -1, -1, 0, 2], 36), ([0, 0, 0, -1, 0, -1, 2], 36), ([0, 0, 0, -1, 0, 2, -1], 36), ([0, 0, 0, -1, 2, 0, -1], 36), ([0, 0, 0, 0, -2, 1, 1], 36), ([1, 0, -1, 2, -1, 0, 0], -36), ([1, 0, -1, 2, 0, -1, 0], 36), ([1, 0, -1, 2, 0, 0, -1], -36), ([1, 0, 0, -2, 0, 1, 1], -36), ([1, 0, 0, -2, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 1, 0], 36), ([1, 0, 0, -1, -1, 0, 2], 36), ([1, 0, 0, -1, -1, 2, 0], -36), ([1, 0, 0, -1, 0, -1, 2], 36), ([1, 0, 0, -1, 0, 2, -1], 36), ([1, 0, 0, -1, 2, -1, 0], -36), ([1, 0, 0, -1, 2, 0, -1], 36), ([1, 0, 0, 0, -2, 1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], -36), ([1, 0, 0, 0, -1, 2, -1], -36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams4 : List (Charge × Coeff) := [(![0, 0, 0, 1, -2, 1], (36, 36)), (![0, 0, 0, 1, 1, -2], (36, 36)), (![0, 0, 0, 2, -1, -1], (0, -36)), (![0, 0, 1, -2, 0, 1], (0, -36)), (![0, 0, 1, -2, 1, 0], (36, 36)), (![0, 0, 1, 0, -2, 1], (0, -36)), (![0, 0, 1, 0, 1, -2], (0, -36)), (![0, 0, 1, 1, -2, 0], (36, 36)), (![0, 0, 1, 1, 0, -2], (0, -36)), (![0, 0, 2, -1, -1, 0], (0, -36)), (![0, 0, 2, -1, 0, -1], (36, 36)), (![0, 0, 2, 0, -1, -1], (36, 36)), (![0, 1, -2, 0, 0, 1], (36, 36)), (![0, 1, -2, 0, 1, 0], (0, -36)), (![0, 1, -2, 1, 0, 0], (36, 36))]

def knownTarget4 : Sparse := [([0, 0, 0, 0, 1, -2, 1], 36), ([0, 0, 0, 0, 1, 1, -2], 36), ([0, 0, 0, 1, -2, 1, 0], 36), ([0, 0, 0, 1, 1, -2, 0], 36), ([0, 0, 0, 2, -1, 0, -1], 36), ([0, 0, 0, 2, 0, -1, -1], 36), ([0, 0, 1, -2, 0, 0, 1], 36), ([0, 0, 1, -2, 1, 0, 0], 36), ([1, 0, 0, 0, 1, -2, 1], 36), ([1, 0, 0, 0, 1, 1, -2], 36), ([1, 0, 0, 0, 2, -1, -1], -36), ([1, 0, 0, 1, -2, 0, 1], -36), ([1, 0, 0, 1, -2, 1, 0], 36), ([1, 0, 0, 1, 0, -2, 1], -36), ([1, 0, 0, 1, 0, 1, -2], -36), ([1, 0, 0, 1, 1, -2, 0], 36), ([1, 0, 0, 1, 1, 0, -2], -36), ([1, 0, 0, 2, -1, -1, 0], -36), ([1, 0, 0, 2, -1, 0, -1], 36), ([1, 0, 0, 2, 0, -1, -1], 36), ([1, 0, 1, -2, 0, 0, 1], 36), ([1, 0, 1, -2, 0, 1, 0], -36), ([1, 0, 1, -2, 1, 0, 0], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams5 : List (Charge × Coeff) := [(![0, 1, 0, -2, 0, 1], (0, -36)), (![0, 1, 0, -2, 1, 0], (0, -36)), (![0, 1, 0, 0, -2, 1], (36, 36)), (![0, 1, 0, 0, 1, -2], (36, 36)), (![0, 1, 0, 1, -2, 0], (0, -36)), (![0, 1, 0, 1, 0, -2], (0, -36)), (![0, 1, 1, -2, 0, 0], (36, 36)), (![0, 1, 1, 0, -2, 0], (0, -36)), (![0, 1, 1, 0, 0, -2], (36, 36)), (![0, 2, -1, -1, 0, 0], (0, -36)), (![0, 2, -1, 0, -1, 0], (36, 36)), (![0, 2, -1, 0, 0, -1], (0, -36)), (![0, 2, 0, -1, -1, 0], (36, 36)), (![0, 2, 0, -1, 0, -1], (36, 36)), (![0, 2, 0, 0, -1, -1], (0, -36))]

def knownTarget5 : Sparse := [([0, 0, 1, 0, 0, -2, 1], 36), ([0, 0, 1, 0, 0, 1, -2], 36), ([0, 0, 1, 1, -2, 0, 0], 36), ([0, 0, 1, 1, 0, 0, -2], 36), ([0, 0, 2, -1, 0, -1, 0], 36), ([0, 0, 2, 0, -1, -1, 0], 36), ([0, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 1, 0, -2, 0, 1], -36), ([1, 0, 1, 0, -2, 1, 0], -36), ([1, 0, 1, 0, 0, -2, 1], 36), ([1, 0, 1, 0, 0, 1, -2], 36), ([1, 0, 1, 0, 1, -2, 0], -36), ([1, 0, 1, 0, 1, 0, -2], -36), ([1, 0, 1, 1, -2, 0, 0], 36), ([1, 0, 1, 1, 0, -2, 0], -36), ([1, 0, 1, 1, 0, 0, -2], 36), ([1, 0, 2, -1, -1, 0, 0], -36), ([1, 0, 2, -1, 0, -1, 0], 36), ([1, 0, 2, -1, 0, 0, -1], -36), ([1, 0, 2, 0, -1, -1, 0], 36), ([1, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 2, 0, 0, -1, -1], -36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams6 : List (Charge × Coeff) := [(![1, -2, 0, 0, 0, 1], (0, -36)), (![1, -2, 0, 0, 1, 0], (36, 36)), (![1, -2, 0, 1, 0, 0], (36, 36)), (![1, -2, 1, 0, 0, 0], (0, -36)), (![1, 0, -2, 0, 0, 1], (36, 36)), (![1, 0, -2, 0, 1, 0], (36, 36)), (![1, 0, -2, 1, 0, 0], (0, -36)), (![1, 0, 0, -2, 0, 1], (36, 36)), (![1, 0, 0, -2, 1, 0], (0, -36)), (![1, 0, 0, 0, -2, 1], (0, -36)), (![1, 0, 0, 0, 1, -2], (0, -36)), (![1, 0, 0, 1, -2, 0], (0, -36)), (![1, 0, 0, 1, 0, -2], (36, 36)), (![1, 0, 1, -2, 0, 0], (0, -36)), (![1, 0, 1, 0, -2, 0], (36, 36))]

def knownTarget6 : Sparse := [([0, 1, -2, 0, 0, 1, 0], 36), ([0, 1, -2, 0, 1, 0, 0], 36), ([0, 1, 0, -2, 0, 0, 1], 36), ([0, 1, 0, -2, 0, 1, 0], 36), ([0, 1, 0, 0, -2, 0, 1], 36), ([0, 1, 0, 0, 1, 0, -2], 36), ([0, 1, 0, 1, 0, -2, 0], 36), ([1, 1, -2, 0, 0, 0, 1], -36), ([1, 1, -2, 0, 0, 1, 0], 36), ([1, 1, -2, 0, 1, 0, 0], 36), ([1, 1, -2, 1, 0, 0, 0], -36), ([1, 1, 0, -2, 0, 0, 1], 36), ([1, 1, 0, -2, 0, 1, 0], 36), ([1, 1, 0, -2, 1, 0, 0], -36), ([1, 1, 0, 0, -2, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], -36), ([1, 1, 0, 0, 0, -2, 1], -36), ([1, 1, 0, 0, 0, 1, -2], -36), ([1, 1, 0, 0, 1, -2, 0], -36), ([1, 1, 0, 0, 1, 0, -2], 36), ([1, 1, 0, 1, -2, 0, 0], -36), ([1, 1, 0, 1, 0, -2, 0], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams7 : List (Charge × Coeff) := [(![1, 0, 1, 0, 0, -2], (36, 36)), (![1, 1, -2, 0, 0, 0], (0, -36)), (![1, 1, 0, -2, 0, 0], (36, 36)), (![1, 1, 0, 0, -2, 0], (36, 36)), (![1, 1, 0, 0, 0, -2], (0, -36)), (![2, -1, -1, 0, 0, 0], (36, 36)), (![2, -1, 0, -1, 0, 0], (0, -36)), (![2, -1, 0, 0, -1, 0], (0, -36)), (![2, -1, 0, 0, 0, -1], (36, 36)), (![2, 0, -1, -1, 0, 0], (36, 36)), (![2, 0, -1, 0, -1, 0], (0, -36)), (![2, 0, -1, 0, 0, -1], (0, -36)), (![2, 0, 0, -1, -1, 0], (36, 36)), (![2, 0, 0, -1, 0, -1], (0, -36)), (![2, 0, 0, 0, -1, -1], (36, 36))]

def knownTarget7 : Sparse := [([0, 1, 0, 1, 0, 0, -2], 36), ([0, 1, 1, 0, -2, 0, 0], 36), ([0, 1, 1, 0, 0, -2, 0], 36), ([0, 2, -1, -1, 0, 0, 0], 36), ([0, 2, -1, 0, 0, 0, -1], 36), ([0, 2, 0, -1, -1, 0, 0], 36), ([0, 2, 0, 0, -1, -1, 0], 36), ([0, 2, 0, 0, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], 36), ([1, 1, 1, -2, 0, 0, 0], -36), ([1, 1, 1, 0, -2, 0, 0], 36), ([1, 1, 1, 0, 0, -2, 0], 36), ([1, 1, 1, 0, 0, 0, -2], -36), ([1, 2, -1, -1, 0, 0, 0], 36), ([1, 2, -1, 0, -1, 0, 0], -36), ([1, 2, -1, 0, 0, -1, 0], -36), ([1, 2, -1, 0, 0, 0, -1], 36), ([1, 2, 0, -1, -1, 0, 0], 36), ([1, 2, 0, -1, 0, -1, 0], -36), ([1, 2, 0, -1, 0, 0, -1], -36), ([1, 2, 0, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -1, 0, -1], -36), ([1, 2, 0, 0, 0, -1, -1], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams8 : List (Charge × Coeff) := [(![-1, -1, 0, 0, 1, 1], (-144, 0)), (![-1, -1, 0, 1, 0, 1], (-144, 0)), (![-1, -1, 0, 1, 1, 0], (0, -144)), (![-1, -1, 1, 0, 0, 1], (144, 144)), (![-1, -1, 1, 0, 1, 0], (-144, 0)), (![-1, -1, 1, 1, 0, 0], (-144, 0)), (![-1, 0, -1, 0, 1, 1], (0, -144)), (![-1, 0, -1, 1, 0, 1], (-144, 0)), (![-1, 0, -1, 1, 1, 0], (-144, 0)), (![-1, 0, 0, -1, 1, 1], (-144, 0)), (![-1, 0, 0, 1, -1, 1], (144, 144)), (![-1, 0, 0, 1, 1, -1], (-144, 0)), (![-1, 0, 1, -1, 0, 1], (-144, 0)), (![-1, 0, 1, -1, 1, 0], (144, 144)), (![-1, 0, 1, 0, -1, 1], (-144, 0))]

def knownTarget8 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -144), ([0, -1, -1, 0, 1, 0, 1], -144), ([0, -1, -1, 1, 0, 0, 1], 144), ([0, -1, -1, 1, 0, 1, 0], -144), ([0, -1, -1, 1, 1, 0, 0], -144), ([0, -1, 0, -1, 1, 0, 1], -144), ([0, -1, 0, -1, 1, 1, 0], -144), ([0, -1, 0, 0, -1, 1, 1], -144), ([0, -1, 0, 0, 1, -1, 1], 144), ([0, -1, 0, 0, 1, 1, -1], -144), ([0, -1, 0, 1, -1, 0, 1], -144), ([0, -1, 0, 1, -1, 1, 0], 144), ([0, -1, 0, 1, 0, -1, 1], -144), ([1, -1, -1, 0, 1, 1, 0], -144), ([1, -1, -1, 1, 0, 0, 1], 144), ([1, -1, 0, -1, 0, 1, 1], -144), ([1, -1, 0, 0, 1, -1, 1], 144), ([1, -1, 0, 1, -1, 1, 0], 144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams9 : List (Charge × Coeff) := [(![-1, 0, 1, 0, 1, -1], (-144, 0)), (![-1, 0, 1, 1, -1, 0], (-144, 0)), (![-1, 0, 1, 1, 0, -1], (0, -144)), (![-1, 1, -1, 0, 0, 1], (-144, 0)), (![-1, 1, -1, 0, 1, 0], (-144, 0)), (![-1, 1, -1, 1, 0, 0], (144, 144)), (![-1, 1, 0, -1, 0, 1], (0, -144)), (![-1, 1, 0, -1, 1, 0], (-144, 0)), (![-1, 1, 0, 0, -1, 1], (-144, 0)), (![-1, 1, 0, 0, 1, -1], (144, 144)), (![-1, 1, 0, 1, -1, 0], (-144, 0)), (![-1, 1, 0, 1, 0, -1], (-144, 0)), (![-1, 1, 1, -1, 0, 0], (-144, 0)), (![-1, 1, 1, 0, -1, 0], (0, -144)), (![-1, 1, 1, 0, 0, -1], (-144, 0))]

def knownTarget9 : Sparse := [([0, -1, 0, 1, 0, 1, -1], -144), ([0, -1, 0, 1, 1, -1, 0], -144), ([0, -1, 1, -1, 0, 0, 1], -144), ([0, -1, 1, -1, 0, 1, 0], -144), ([0, -1, 1, -1, 1, 0, 0], 144), ([0, -1, 1, 0, -1, 1, 0], -144), ([0, -1, 1, 0, 0, -1, 1], -144), ([0, -1, 1, 0, 0, 1, -1], 144), ([0, -1, 1, 0, 1, -1, 0], -144), ([0, -1, 1, 0, 1, 0, -1], -144), ([0, -1, 1, 1, -1, 0, 0], -144), ([0, -1, 1, 1, 0, 0, -1], -144), ([1, -1, 0, 1, 1, 0, -1], -144), ([1, -1, 1, -1, 1, 0, 0], 144), ([1, -1, 1, 0, -1, 0, 1], -144), ([1, -1, 1, 0, 0, 1, -1], 144), ([1, -1, 1, 1, 0, -1, 0], -144)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -2, -1, 0, 0, 1, 2], 18), ([0, -2, -1, 0, 1, 0, 2], -18), ([0, -2, -1, 1, 0, 0, 2], 18), ([0, -2, 0, -1, 0, 1, 2], 18), ([0, -2, 0, -1, 1, 0, 2], 18), ([0, -2, 0, 0, 1, -1, 2], 18), ([0, -2, 0, 0, 1, 0, 1], 18), ([0, -2, 0, 1, -1, 0, 2], 18), ([0, -2, 0, 1, 0, -1, 2], -18), ([0, -2, 0, 1, 0, 0, 1], 18), ([0, -2, 1, 0, -1, 0, 2], 18), ([0, -2, 1, 0, 0, -1, 2], 18), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, -1, 0, 0, 0, -1, 2], 18), ([1, -2, -1, 0, 1, 0, 2], -18), ([1, -2, 0, 0, -1, 1, 2], 18), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -2, 0, 1, 0, -1, 2], -18), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -2, 1, -1, 0, 0, 2], 18), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 0, 0, -1, 2], 18)]

def source1 : Sparse := [([0, -3, 0, 0, 0, 3, 0], 36), ([0, -2, -1, 0, 1, 2, 0], 18), ([0, -2, -1, 1, 0, 2, 0], 18), ([0, -2, 0, -1, 0, 2, 1], 18), ([0, -2, 0, 0, -1, 2, 1], 18), ([0, -2, 0, 0, 1, 2, -1], 18), ([0, -2, 0, 1, -1, 2, 0], 18), ([0, -2, 0, 1, 0, 1, 0], 18), ([0, -2, 0, 1, 0, 2, -1], -18), ([0, -2, 1, -1, 0, 2, 0], 18), ([0, -2, 1, 0, -1, 2, 0], -18), ([0, -2, 1, 0, 0, 1, 0], 18), ([0, -2, 1, 0, 0, 2, -1], 18), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 0, 0, 2, -1], 18), ([1, -2, -1, 0, 0, 2, 1], 18), ([1, -2, 0, -1, 1, 2, 0], 18), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -2, 0, 1, 0, 2, -1], -18), ([1, -2, 1, 0, -1, 2, 0], -18), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, -1, 0, 0, 0, 2, -1], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source10 : Sparse := [([0, -1, 0, -2, 0, 2, 1], 18), ([0, -1, 0, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 0, 2, 1], 18), ([0, 0, -1, -2, 1, 2, 0], -18), ([0, 0, -1, -1, 0, 2, 0], 18), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 0, 0, -2, 1, 2, -1], 18), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 1, -2, -1, 2, 0], 18), ([0, 0, 1, -2, 0, 2, -1], 18), ([0, 1, -1, -2, 0, 2, 0], 18), ([0, 1, 0, -2, -1, 2, 0], 18), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 1, 0, -2, 0, 2, -1], -18), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 1, -2, 0, 2, 0], 18), ([1, 0, -1, -2, 1, 2, 0], -18), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 0, 0, -2, -1, 2, 1], 18), ([1, 0, 0, -2, 0, 1, 1], -18), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 1, -2, 0, 1, 0], -18), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 1, 0, -2, 0, 2, -1], -18)]

def source11 : Sparse := [([0, -1, 0, -2, 2, 0, 1], 18), ([0, -1, 0, -2, 2, 1, 0], -18), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 1, -2, 2, 0, 0], 18), ([0, 0, -1, -2, 2, 0, 1], 18), ([0, 0, -1, -2, 2, 1, 0], 18), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 0, 0, -2, 2, 1, -1], 18), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 1, -2, 1, 0, 0], 18), ([0, 0, 1, -2, 2, -1, 0], 18), ([0, 0, 1, -2, 2, 0, -1], -18), ([0, 1, 0, -2, 2, -1, 0], 18), ([0, 1, 0, -2, 2, 0, -1], 18), ([1, -1, 0, -2, 2, 1, 0], -18), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 0, 0, -2, 1, 0, 1], -18), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 0, 0, -2, 2, -1, 1], 18), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 1, -2, 1, 0, 0], 18), ([1, 0, 1, -2, 2, 0, -1], -18), ([1, 1, -1, -2, 2, 0, 0], 18), ([1, 1, 0, -2, 1, 0, 0], -18)]

def source12 : Sparse := [([0, -1, 0, 0, -2, 1, 2], 18), ([0, -1, 1, 0, -2, 0, 2], 18), ([0, 0, -1, 0, -2, 1, 2], 18), ([0, 0, -1, 0, -1, 0, 2], 18), ([0, 0, -1, 1, -2, 0, 2], 18), ([0, 0, 0, -1, -2, 1, 2], -18), ([0, 0, 0, -1, -1, 0, 2], 18), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 0, 0, 1, -2, -1, 2], 18), ([0, 0, 1, -1, -2, 0, 2], 18), ([0, 1, -1, 0, -2, 0, 2], -18), ([0, 1, 0, -1, -2, 0, 2], 18), ([0, 1, 0, 0, -2, -1, 2], 18), ([0, 1, 0, 0, -2, 0, 1], 18), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 1, -2, 0, 2], 18), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 0, 0, -1, -2, 1, 2], -18), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 0, 1, -2, 0, 1], -18), ([1, 0, 1, 0, -2, -1, 2], 18), ([1, 0, 1, 0, -2, 0, 1], -18), ([1, 1, -1, 0, -2, 0, 2], -18), ([1, 1, 0, 0, -2, 0, 1], 18)]

def source13 : Sparse := [([0, -1, 0, 0, -2, 2, 1], -18), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 1, -2, 2, 0], 18), ([0, -1, 1, 0, -2, 2, 0], 18), ([0, 0, -1, 0, -2, 2, 1], 18), ([0, 0, -1, 0, -1, 2, 0], 18), ([0, 0, -1, 1, -2, 2, 0], -18), ([0, 0, 0, -1, -2, 2, 1], 18), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 0, 0, 1, -2, 1, 0], 18), ([0, 0, 0, 1, -2, 2, -1], 18), ([0, 0, 1, -1, -2, 2, 0], 18), ([0, 1, -1, 0, -2, 2, 0], 18), ([0, 1, 0, 0, -2, 2, -1], 18), ([1, -1, 0, 0, -2, 2, 1], -18), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 0, -1, 1, -2, 2, 0], -18), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 0, 1, -2, 1, 0], 18), ([1, 0, 1, 0, -2, 1, 0], -18), ([1, 0, 1, 0, -2, 2, -1], 18), ([1, 1, 0, -1, -2, 2, 0], 18), ([1, 1, 0, 0, -2, 1, 0], -18)]

def source14 : Sparse := [([0, -1, 0, 0, 0, -1, 2], 18), ([0, -1, 0, 0, 1, -2, 2], 18), ([0, -1, 0, 1, 0, -2, 2], 18), ([0, -1, 1, 0, 0, -2, 2], -18), ([0, 0, -1, 0, 1, -2, 2], 18), ([0, 0, 0, -1, 0, -1, 2], 18), ([0, 0, 0, -1, 1, -2, 2], -18), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 0, 0, 1, -1, -2, 2], 18), ([0, 0, 1, -1, 0, -2, 2], 18), ([0, 0, 1, 0, -1, -2, 2], 18), ([0, 0, 1, 0, 0, -2, 1], 18), ([0, 1, -1, 0, 0, -2, 2], 18), ([0, 1, 0, -1, 0, -2, 2], 18), ([1, -1, 0, 0, 0, -1, 2], 18), ([1, -1, 1, 0, 0, -2, 2], -18), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 0, -1, 1, 0, -2, 2], 18), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 0, 0, -1, 1, -2, 2], -18), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 0, 0, 1, 0, -2, 1], -18), ([1, 0, 1, 0, 0, -2, 1], 18), ([1, 1, 0, 0, -1, -2, 2], 18), ([1, 1, 0, 0, 0, -2, 1], -18)]

def source15 : Sparse := [([0, -1, 0, 0, 0, 2, -1], 18), ([0, -1, 0, 0, 1, 2, -2], -18), ([0, -1, 0, 1, 0, 2, -2], 18), ([0, -1, 1, 0, 0, 2, -2], 18), ([0, 0, -1, 0, 1, 2, -2], 18), ([0, 0, -1, 1, 0, 2, -2], 18), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 0, -1, 1, 2, -2], 18), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 0, 1, -1, 0, 2, -2], -18), ([0, 0, 1, 0, -1, 2, -2], 18), ([0, 0, 1, 0, 0, 1, -2], 18), ([0, 1, 0, -1, 0, 2, -2], 18), ([0, 1, 0, 0, -1, 2, -2], 18), ([1, -1, 0, 0, 0, 2, -1], 18), ([1, -1, 0, 0, 1, 2, -2], -18), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 0, 0, 1, -1, 2, -2], 18), ([1, 0, 0, 1, 0, 1, -2], -18), ([1, 0, 1, -1, 0, 2, -2], -18), ([1, 0, 1, 0, 0, 1, -2], 18), ([1, 1, -1, 0, 0, 2, -2], 18), ([1, 1, 0, 0, 0, 1, -2], -18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source100 : Sparse := [([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 2, 0, -1, 0], -36), ([0, 1, -2, 2, 0, -1, 0], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, -1, 2, 0, -2, 0], 36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 2, -1, 1, 0, -2, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, 0, -1, 0], -36), ([1, 1, -2, 1, 0, 0, 0], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, -1, 2, 0, -2, 0], 36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 2, -2, 1, 0, -1, 0], -36), ([1, 2, -1, 0, 0, -1, 0], 36)]

def source101 : Sparse := [([0, 0, -1, 1, 1, 0, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, -1, 2, 0, 0, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 2, -2, 1, 0, 0, -1], -36), ([0, 2, -1, 0, 0, 0, -1], -36), ([0, 2, -1, 1, 0, 0, -2], 36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, 0, 0, -1], 36), ([1, 1, -2, 1, 0, 0, 0], 36), ([1, 1, -2, 2, 0, 0, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 2, -1, 0, 0, 0, -1], -36), ([1, 2, -1, 1, 0, 0, -2], 36)]

def source102 : Sparse := [([0, 0, 0, -1, -1, 0, 2], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, 0, -2, -1, 0, 2], -36), ([0, 1, 0, -2, 0, 0, 1], -36), ([0, 1, 0, -1, -2, 0, 2], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -2, 0, 1], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 2, 0, -2, -1, 0, 1], -36), ([0, 2, 0, -1, -2, 0, 1], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([1, 0, 0, -1, -1, 0, 2], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, 0, -2, 0, 0, 1], -36), ([1, 1, 0, 0, -2, 0, 1], -36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 2, 0, -1, -1, 0, 0], -36)]

def source103 : Sparse := [([0, 0, 0, -1, -1, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, 0, -2, -1, 2, 0], -36), ([0, 1, 0, -2, 0, 1, 0], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 2, 0, -2, -1, 1, 0], 36), ([0, 2, 0, -1, -2, 1, 0], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([1, 0, 0, -1, -1, 2, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, 0, -2, 0, 1, 0], -36), ([1, 1, 0, -1, -2, 2, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 2, 0, -2, -1, 1, 0], 36), ([1, 2, 0, -1, -1, 0, 0], -36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source104 : Sparse := [([0, 0, 0, -1, 0, -1, 2], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, 0, -2, 0, -1, 2], 36), ([0, 1, 0, -2, 0, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, -2, 2], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 2, 0, -2, 0, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, 0, -2, 0, -1, 2], 36), ([1, 1, 0, -2, 0, 0, 1], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 0, -2, 1], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 2, 0, -1, 0, -2, 1], -36), ([1, 2, 0, -1, 0, -1, 0], 36)]

def source105 : Sparse := [([0, 0, 0, -1, 0, 2, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -2, 0, 1, 0], -36), ([0, 1, 0, -2, 0, 2, -1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, 2, -2], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 2, 0, -2, 0, 1, -1], -36), ([1, 0, 0, -1, 0, 2, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, 0, -2, 0, 1, 0], -36), ([1, 1, 0, -2, 0, 2, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 0, 0, 1, -2], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 2, 0, -1, 0, 0, -1], 36), ([1, 2, 0, -1, 0, 1, -2], -36)]

def source106 : Sparse := [([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, 0, -2, 2, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, -1, 2, -2, 0], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 2, 0, -2, 1, -1, 0], -36), ([0, 2, 0, -1, 1, -2, 0], -36), ([1, 0, 0, -1, 2, -1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, 0, -2, 1, 0, 0], 36), ([1, 1, 0, 0, 1, -2, 0], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, -1, 0, -1, 0], 36)]

def source107 : Sparse := [([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 0, -1, 2, 0, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, 0, -2, 2, 0, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, -1, 2, 0, -2], 36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 0, 1, 0, -2], -36), ([0, 2, 0, -1, 1, 0, -2], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 0, -1, 2, 0, -1], -36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, 0, -2, 1, 0, 0], 36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, -1, 2, 0, -2], 36), ([1, 1, 0, 0, 1, 0, -2], -36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, -2, 1, 0, -1], -36), ([1, 2, 0, -1, 0, 0, -1], 36)]

def source108 : Sparse := [([0, 0, 1, 0, -1, -1, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -2, -1, 2], -36), ([0, 1, 0, 0, -2, 0, 1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 2, 0, 0, -2, -1, 1], 36), ([0, 2, 0, 0, -1, -2, 1], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([1, 0, 0, 0, -1, -1, 2], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, 0, -2, 0, 1], -36), ([1, 1, 0, 0, -1, -2, 2], -36), ([1, 1, 0, 0, 0, -2, 1], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -2, -1, 1], 36), ([1, 2, 0, 0, -1, -1, 0], -36)]

def source109 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, 0, -2, 2, -1], -36), ([0, 1, 0, 0, -1, 2, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 2, 0, 0, -2, 1, -1], -36), ([0, 2, 0, 0, -1, 1, -2], -36), ([1, 0, 0, 0, -1, 2, -1], 36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -2, 1, 0], 36), ([1, 1, 0, 0, 0, 1, -2], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 2, 0, 0, -1, 0, -1], 36)]

def source110 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, 0, 1, 0, -2], -36), ([0, 1, 0, 0, 2, -1, -2], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 0, 0, 1, -2, -1], -36), ([0, 2, 0, 0, 1, -1, -2], 36), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 1, -2, 0], 36), ([1, 1, 0, 0, 1, 0, -2], -36), ([1, 1, 0, 0, 2, -2, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, 0, 0, -1, -1], -36), ([1, 2, 0, 0, 1, -1, -2], 36)]

def source111 : Sparse := [([0, 0, 1, 1, -1, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 2, -1, -2, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([0, 2, 0, 1, -2, -1, 0], -36), ([0, 2, 0, 1, -1, -2, 0], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, 0, 1, -2, 0, 0], 36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 2, -2, -1, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, -1, 0], -36), ([1, 2, 0, 1, -1, -2, 0], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source112 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 1, 0, 2, -2, 0, -1], -36), ([0, 1, 0, 2, -1, 0, -2], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 1, -1, 0, -2], -36), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 1, -2, 0, 0], 36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 1, 0, 2, -1, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, 0, -1], 36), ([1, 2, 0, 1, -2, 0, -1], -36)]

def source113 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -36), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 1, 0, 2, 0, -2, -1], -36), ([0, 1, 0, 2, 0, -1, -2], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 0, 1, 0, -2, -1], -36), ([0, 2, 0, 1, 0, -1, -2], -36), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, 0, -1, -1], -36)]

def source114 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 2, -1, -2, 0, 0], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([0, 2, 1, -2, -1, 0, 0], -36), ([0, 2, 1, -1, -2, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 2, -1, -1, 0, 0], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 2, -2, -1, 0, 0], -36), ([1, 2, 0, -1, -1, 0, 0], -36), ([1, 2, 1, -1, -2, 0, 0], 36)]

def source115 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 2, -1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 2, -2, 0, -1, 0], -36), ([0, 1, 2, -1, 0, -2, 0], 36), ([0, 2, 1, -1, 0, -2, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 2, -1, 0, -1, 0], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 2, -1, 0, -2, 0], 36), ([1, 2, 0, -1, 0, -1, 0], 36), ([1, 2, 1, -2, 0, -1, 0], -36)]

def source116 : Sparse := [([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 2, -2, 0, 0, -1], -36), ([0, 1, 2, -1, 0, 0, -2], -36), ([0, 2, 1, -2, 0, 0, -1], -36), ([0, 2, 1, -1, 0, 0, -2], -36), ([1, 0, 2, -1, 0, 0, -1], 36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 2, 0, -1, 0, 0, -1], 36)]

def source117 : Sparse := [([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 2, 0, -1, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, -2, -1, 0], -36), ([0, 1, 2, 0, -1, -2, 0], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([0, 2, 1, 0, -2, -1, 0], -36), ([0, 2, 1, 0, -1, -2, 0], -36), ([1, 0, 2, 0, -1, -1, 0], -36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, -1, 0], -36)]

def source118 : Sparse := [([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 2, 0, -1, 0, -1], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, -2, 0, -1], 36), ([0, 1, 2, 0, -1, 0, -2], -36), ([0, 2, 1, 0, -2, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 2, 0, -1, 0, -1], -36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 1, 2, 0, -2, 0, -1], 36), ([1, 2, 0, 0, -1, 0, -1], 36), ([1, 2, 1, 0, -1, 0, -2], -36)]

def source119 : Sparse := [([0, 0, 1, 1, 0, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, 0, -2, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 1, 0, 0, -2, -1], 36), ([0, 2, 1, 0, 0, -1, -2], -36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 2, 0, 0, -1, -1], 36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 1, 2, 0, 0, -1, -2], -36), ([1, 2, 0, 0, 0, -1, -1], -36), ([1, 2, 1, 0, 0, -2, -1], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source120 : Sparse := [([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 2, -1, -2, 0, 0], 9), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], 18), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 1, 1, -2, -1, 0, 1], 9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 2, -2, -1, 0, 0], 9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], 18)]

def source121 : Sparse := [([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], 9), ([0, -1, -2, 2, 1, 0, 0], -9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9)]

def source122 : Sparse := [([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 1, 1, -2, 1, -1, 0], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 2, -2, 0, -1, 0], 9), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -2, 0], -9), ([0, 1, 2, -1, 0, -1, -1], 9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 1, 1, -2, 0, -1, 1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, 0, -2, 0], -9), ([1, 2, 0, -1, 0, -1, 0], -18)]

def source123 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -1, -2, 1, 0, 2, 0], 9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9)]

def source124 : Sparse := [([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 1, 1, -2, 1, 0, -1], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, -1, 0, 1, -2], -9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 2, -2, 0, 0, -1], 9), ([0, 1, 2, -1, -1, 0, -1], -9), ([0, 1, 2, -1, 0, -1, -1], -9), ([0, 1, 2, -1, 0, 0, -2], 9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -2, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 2, -1, -1, 0, -1], -9), ([1, 1, 2, -1, 0, -1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

def source125 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -2, 1, 0, 0, 2], 9), ([0, -1, -2, 2, 0, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

def source126 : Sparse := [([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, 0, -2, -1, 1], -9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, -2, 1], 9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, 0, -2, -1, 0], 9), ([0, 1, 2, 0, -1, -2, 0], 9), ([0, 2, 0, 0, -1, -1, 0], 18), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, -2, 1], 9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, -1, -1, 0], 9), ([1, 1, 2, 0, -1, -1, -1], 9), ([1, 2, 0, 0, -1, -1, 0], 18)]

def source127 : Sparse := [([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], 9), ([0, -1, -2, 0, 2, 1, 0], 9), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source128 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, 1, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 1, 2, 0, -2, 0, -1], -9), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 1, 2, 0, -1, 0, -2], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 1, 2, 0, -2, 0, -1], -9), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

def source129 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -2, 0, 1, 0, 2], 9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], 9), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 1, 0, 0], 9)]

def source130 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 1, 2, 0, 0, -2, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

def source131 : Sparse := [([0, -1, -2, 0, 0, 1, 2], -9), ([0, -1, -2, 0, 0, 2, 1], 9), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -2, 0, 0, 1, 2], -9), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -9)]

def source132 : Sparse := [([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 2, -1, 0, 0], 9), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 2, -2, 0, 0], 9), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, -1, 2, -1, 0, -1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 2, -1, 0, -1, 0, 0], -18)]

def source133 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 18), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 2, 0, 0], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 2, -2, 1, 0, 0], 9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9)]

def source134 : Sparse := [([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -2, 2, 0, -1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, -1, -1, 0], 9), ([0, 1, -1, 2, 0, -2, 0], -9), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 1, 0, -2, 0], 9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, 0, -2, 0], -9), ([1, 1, -1, 2, 0, -1, -1], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], -18)]

def source135 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 18), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 2, -2, 0, 1, 0], 9), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 0, 2, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source136 : Sparse := [([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, -1, 2, 0, -1, -1], 9), ([0, 1, -1, 2, 0, 0, -2], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -2, 2, 0, 0, -1], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 2, -1, 0, 0, 0, -1], 18)]

def source137 : Sparse := [([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 1, -2, 0, 0, 2], 9), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 2, -2, 0, 0, 1], -9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 2, -2, 0, 0, 1], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9)]

def source138 : Sparse := [([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, 0, 1, -2, -1, 1], 9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 2, -1, -2, 0], 9), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, 0, 0, -1, -1, 0], 18), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -2, 1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 2, -2, -1, 0], 9), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, 0, 0, -1, -1, 0], 18)]

def source139 : Sparse := [([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -2, 1, 2, 0], 9), ([0, -1, 0, -2, 2, 1, 0], -9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], -9), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, 0, -2, 2, 1, 0], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 2, -1], -9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9)]

def source140 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 0, 2, -2, 0, -1], 9), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 0, 2, -1, 0, -2], -9), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

def source141 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, 0, -2, 2, 0, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 1, 0, 1], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, 0, -2, 1, 0, 2], 9), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 9)]

def source142 : Sparse := [([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 0, 2, 0, -2, -1], 9), ([0, 1, 0, 2, 0, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

def source143 : Sparse := [([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, 0, -2, 0, 1, 2], 9), ([0, -1, 0, -2, 0, 2, 1], 9), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 0, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 0, 1, 0], -9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source144 : Sparse := [([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, -1, 2, 0, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -2, 2, 0, 0], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 2, -1, -1, 0, 0, 0], 18)]

def source145 : Sparse := [([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 2, -2, 0, 0], -9), ([0, -1, 2, 1, -2, 0, 0], 9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 2, -2, 0, 0], -9), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9)]

def source146 : Sparse := [([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 0, 2, -1, 0], -9), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 2, -2, 0], 9), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -2, 0, 2, -1, 0], -9), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], -18)]

def source147 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 18), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, 0, -2, 2, 0], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], 9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, 0, -1, 0, 0], 9)]

def source148 : Sparse := [([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 0, 2, 0, -1], 9), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 0, 2, 0, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 2, -1, 0, 0, 0, -1], 18)]

def source149 : Sparse := [([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, 0, -2, 0, 2], 9), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 2, 0, -2, 0, 1], 9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, 0, -1, 0, 0], -9)]

def source150 : Sparse := [([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 2, -1, 0], -9), ([0, 1, 0, -2, 2, -1, 0], 9), ([0, 1, 0, -1, 1, -2, 1], -9), ([0, 1, 0, -1, 2, -2, 0], 9), ([0, 1, 0, -1, 2, -1, -1], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, -2, 1, -1, 0], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 2, -1, 0], -9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, 0, -2, 1, -1, 1], -9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, -1, 2, -1, -1], -9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, 0, -1, 0, -1, 0], -18)]

def source151 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 18), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -2, 2, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 2, -2, 1, 0], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 1, -1, 0, 0], 9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source152 : Sparse := [([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], -9), ([0, 1, 0, -2, 2, 0, -1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, -1, 2, -1, -1], 9), ([0, 1, 0, -1, 2, 0, -2], -9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 1, -2, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -2, 1, 1, -1], -9), ([1, 1, 0, -1, 1, 1, -2], -9), ([1, 1, 0, -1, 2, 0, -2], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

def source153 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 2, -2, 0, 1], 9), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 1, -2, 0, 2], 9), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -2, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9)]

def source154 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 0, 0, 2, -1, -2], 9), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 0, 0, 2, -2, -1], 9), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

def source155 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, 0, -2, 1, 2], 9), ([0, -1, 0, 0, -2, 2, 1], -9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, 0, -2, 2, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, 0, -1, 1, 0], -9)]

def source156 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 0, 2, 0], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 2, 0], 9), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 2, -1, -1, 0, 0, 0], 18)]

def source157 : Sparse := [([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 1, 2, 0, -2, 0], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -9)]

def source158 : Sparse := [([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 1, -2, 0, -1, 2, 0], -9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, 0, -2, 2, 0], 9), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, 0, 0, -1, 1, -1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, -1, 2, 0], -9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 2, -1, 0, -1, 0, 0], -18)]

def source159 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 2, -2, 0], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, -1, 2, 0, 1, -2, 0], 9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source16 : Sparse := [([0, -1, 0, 0, 2, -2, 1], 18), ([0, -1, 0, 0, 2, -1, 0], 18), ([0, -1, 0, 1, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -2, 0], 18), ([0, 0, -1, 0, 2, -2, 1], -18), ([0, 0, -1, 0, 2, -1, 0], 18), ([0, 0, -1, 1, 2, -2, 0], 18), ([0, 0, 0, -1, 2, -2, 1], 18), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 1, 1, -2, 0], 18), ([0, 0, 0, 1, 2, -2, -1], 18), ([0, 0, 1, 0, 2, -2, -1], 18), ([0, 1, -1, 0, 2, -2, 0], 18), ([0, 1, 0, -1, 2, -2, 0], 18), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 0, 1, 2, -2, 0], -18), ([1, 0, -1, 0, 2, -2, 1], -18), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 0, 1, 1, -2, 0], 18), ([1, 0, 1, -1, 2, -2, 0], 18), ([1, 0, 1, 0, 1, -2, 0], -18), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 1, 0, 0, 2, -2, -1], 18)]

def source17 : Sparse := [([0, -1, 0, 0, 2, 1, -2], 18), ([0, -1, 0, 1, 2, 0, -2], 18), ([0, 0, -1, 0, 2, 0, -1], 18), ([0, 0, -1, 0, 2, 1, -2], -18), ([0, 0, -1, 1, 2, 0, -2], 18), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 0, -1, 2, 1, -2], 18), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 1, -1, 2, 0, -2], 18), ([0, 0, 1, 0, 2, -1, -2], 18), ([0, 1, -1, 0, 2, 0, -2], 18), ([0, 1, 0, -1, 2, 0, -2], -18), ([0, 1, 0, 0, 1, 0, -2], 18), ([0, 1, 0, 0, 2, -1, -2], 18), ([1, -1, 0, 0, 2, 0, -1], -18), ([1, -1, 1, 0, 2, 0, -2], 18), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 0, -1, 0, 2, 1, -2], -18), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 0, 1, 1, 0, -2], -18), ([1, 0, 0, 1, 2, -1, -2], 18), ([1, 0, 1, 0, 1, 0, -2], -18), ([1, 1, 0, -1, 2, 0, -2], -18), ([1, 1, 0, 0, 1, 0, -2], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source160 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -2, 0, 0, 2, -1], 9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 0, 0, 2, -2], 9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 2, -1, 0, 0, 0, -1], 18)]

def source161 : Sparse := [([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -2, 2], -9), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, -1, 2, 0, 0, -2, 1], 9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, 0, -2, 2], -9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9)]

def source162 : Sparse := [([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, 0, -2, -1, 1, 1], -9), ([0, 1, 0, -2, -1, 2, 0], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, -2, 1, 1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], 18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -2, 1, 1], 9), ([1, 1, 0, -1, -2, 2, 0], 9), ([1, 1, 0, -1, -1, 2, -1], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, 0, -1, -1, 0, 0], 18)]

def source163 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 0, 1, 2, -2, 0], -9), ([0, -1, 0, 2, 1, -2, 0], 9), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 1, 2, -2, 0], -9), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9)]

def source164 : Sparse := [([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 2, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -2, 0, 2, -1], -9), ([0, 1, 0, -1, -1, 2, -1], 9), ([0, 1, 0, -1, 0, 2, -2], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, -1, 0, 1, -2], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 0, 2, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -2, 0, 2, -1], -9), ([1, 1, 0, -2, 1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, -1, 1, 1, -2], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 1, -2, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

def source165 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, 0, -2, 2], 9), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], 9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -1, 0], 9)]

def source166 : Sparse := [([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 1, -1, 0, -1, 2, -1], -9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, -1, 2, -1], -9), ([0, 1, 0, 0, -2, 2, -1], 9), ([0, 1, 0, 0, -1, 2, -2], 9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 1, 0, -1, 1, -2], -9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, -1, 2, -1], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, -1, 2, -1], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

def source167 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 1, -2, 2], 9), ([0, -1, 0, 0, 2, -2, 1], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -2, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -2, 1], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 0, 1, -1, 0], 9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source168 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], 9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 0, 2], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 2, -1, -1, 0, 0, 0], 18)]

def source169 : Sparse := [([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 1, 2, 0, 0, -2], 9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, -1, 2, 1, 0, 0, -2], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, -1, 2, 1, 0, 0, -2], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined5_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 27), ([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], -27), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], -18), ([0, -1, -2, 0, 1, 0, 2], -27), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], -27), ([1, -2, -1, 0, 1, 0, 2], 27), ([1, -2, -1, 1, 1, 0, 1], -9), ([1, -2, 0, 0, 1, 0, 1], -18)]

def combined5_part1 : Sparse := [([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], -27), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, 0, -2, 0, 1, 0, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 1, 0, 0], 9)]

def combined5 : Sparse := combined5_part0 ++ combined5_part1

def combined6_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 18), ([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], -27), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], -9), ([0, -1, -2, 0, 1, 0, 2], -18), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 18), ([0, -1, -1, 0, 0, 0, 2], -18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, -1, 2], -18), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -27), ([1, -2, -1, 0, 1, 0, 2], 18)]

def combined6_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 0, 1], -18), ([1, -2, 0, 0, 1, 0, 1], -9), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], -27), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 1, 1], 9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], -18), ([1, -1, -1, 0, 1, -1, 2], -18), ([1, -1, -1, 0, 1, 1, 0], -27), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -2, 0, 1, 0, 1], 9), ([1, 0, -1, -1, 1, 0, 1], -27), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], 9)]

def combined6 : Sparse := combined6_part0 ++ combined6_part1

def combined7_part0 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 18), ([0, -2, -1, 0, 1, 1, 1], 18), ([0, -2, -1, 0, 2, 0, 1], -18), ([0, -2, -1, 1, 1, 0, 1], -18), ([0, -1, -2, 0, 1, 0, 2], -18), ([0, -1, -2, 1, 1, 0, 1], 18), ([0, -1, -1, -1, 1, 0, 2], 18), ([0, -1, -1, 0, 0, 1, 1], -18), ([0, -1, -1, 0, 1, -1, 2], -18), ([0, -1, -1, 0, 2, -1, 1], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, 0, -1, 0, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], -18), ([1, -2, -1, 0, 1, 0, 2], 18), ([1, -2, -1, 1, 1, 0, 1], -18), ([1, -1, -2, 0, 1, 1, 1], 18), ([1, -1, -2, 0, 2, 0, 1], -18), ([1, -1, -1, -1, 2, 0, 1], 18), ([1, -1, -1, 0, 1, -1, 2], -18)]

def combined7_part1 : Sparse := [([1, -1, -1, 0, 1, 1, 0], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, 0, -1, -1, 1, 0, 1], -18), ([1, 0, -1, 0, 1, 0, 0], 18)]

def combined7 : Sparse := combined7_part0 ++ combined7_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined8_part0 : Sparse := [([0, -2, -1, 0, 1, 2, 0], -36), ([0, -2, -1, 0, 2, 1, 0], -36), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], -27), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27), ([1, -2, 0, 0, 1, 1, 0], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], 27), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 1, 1], -9)]

def combined8_part1 : Sparse := [([1, -1, -1, 0, 0, 2, 0], 27), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], 27), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, 0, -2, 0, 1, 1, 0], 36), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined8 : Sparse := combined8_part0 ++ combined8_part1

def combined9_part0 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 1, 2, 0], -27), ([0, -2, -1, 0, 2, 1, 0], -27), ([0, -2, -1, 1, 1, 1, 0], -9), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], -27), ([0, -1, -2, 0, 2, 1, 0], -27), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 0, 1, 1], -27), ([0, -1, -1, 0, 1, 0, 1], -27), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, 0, -1, -1, 1, 1, 0], -27), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], -27)]

def combined9_part1 : Sparse := [([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], 18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], 18), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], 18), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], 18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, 0, -2, 0, 1, 1, 0], 18), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

def combined9 : Sparse := combined9_part0 ++ combined9_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined48_part0 : Sparse := [([0, -2, 0, 1, -1, 0, 2], -36), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -2, 0, 2, -1, 0, 1], 36), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 2, -2, 0, 1], -27), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -27), ([0, 0, 0, 1, -1, 0, 0], 9), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -2, 0, 2, -1, 0, 1], 36), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -27), ([1, -1, -1, 1, 0, 0, 1], 36)]

def combined48_part1 : Sparse := [([1, -1, 0, 0, -1, 0, 2], 27), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 1, -2, 0, 2], -27), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 1, -2, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, -1, -1, 1], -27)]

def combined48 : Sparse := combined48_part0 ++ combined48_part1

def combined49_part0 : Sparse := [([0, -2, 0, 1, -1, 0, 2], -27), ([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -2, 0, 2, -1, 0, 1], 36), ([0, -2, 1, 1, -1, 0, 1], 9), ([0, -1, -1, 1, -1, 0, 2], 18), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 1, -2, 1, 1], 18), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 0, 2, -2, 0, 1], -27), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 0, 2, -1, 0, 0], -9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, -1, 0, 0], 9)]

def combined49_part1 : Sparse := [([1, -2, 0, 1, 0, 0, 1], -9), ([1, -2, 0, 2, -1, 0, 1], 36), ([1, -2, 1, 1, -1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, 0, 0, -1, 0, 2], 27), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 1, -2, 0, 2], -18), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, -1, 2], 18), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, -1, 0, 0], -9), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 1, -2, 0, 1], 18), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 1, -2, 0, 1], 27), ([1, 0, 0, 1, -1, -1, 1], -18)]

def combined49 : Sparse := combined49_part0 ++ combined49_part1

def combined50_part0 : Sparse := [([0, -2, 0, 1, -1, 0, 2], -18), ([0, -2, 0, 1, -1, 1, 1], -18), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -2, 0, 2, -1, 0, 1], 27), ([0, -2, 1, 1, -1, 0, 1], 18), ([0, -1, -1, 1, -1, 0, 2], 18), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, -1, 0, 1, -2, 1, 1], 18), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 2, -2, 0, 1], -27), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([1, -2, 0, 1, -1, 1, 1], -9), ([1, -2, 0, 1, 0, 0, 1], -9)]

def combined50_part1 : Sparse := [([1, -2, 0, 2, -1, 0, 1], 27), ([1, -2, 1, 1, -1, 0, 1], 9), ([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 2, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], 18), ([1, -1, 0, 1, -2, 0, 2], -18), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, -1, 2], 18), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 1, -2, 0, 1], 18), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 1, -2, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], -18)]

def combined50 : Sparse := combined50_part0 ++ combined50_part1

def combined51_part0 : Sparse := [([0, -2, 0, 1, -1, 0, 2], -18), ([0, -2, 0, 1, -1, 1, 1], -18), ([0, -2, 0, 2, -1, 0, 1], 18), ([0, -2, 1, 1, -1, 0, 1], 18), ([0, -1, -1, 1, -1, 0, 2], 18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, -1, 0, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, -1, 0, 1, -2, 1, 1], 18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 2, -2, 0, 1], -18), ([0, -1, 0, 2, -1, -1, 1], 18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, 0, -1, 1, -1, 0, 1], -18), ([0, 0, 0, 1, -1, 0, 0], 18), ([1, -2, 0, 1, -1, 1, 1], -18), ([1, -2, 0, 2, -1, 0, 1], 18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 2, -1, 0, 1], -18), ([1, -1, 0, 1, -2, 0, 2], -18), ([1, -1, 0, 1, -1, -1, 2], 18)]

def combined51_part1 : Sparse := [([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 1, -2, 0, 1], 18), ([1, 0, 0, 0, -1, 0, 1], 18), ([1, 0, 0, 1, -1, -1, 1], -18)]

def combined51 : Sparse := combined51_part0 ++ combined51_part1

def combined52_part0 : Sparse := [([0, -2, 0, 1, -1, 2, 0], -36), ([0, -2, 0, 1, 0, 1, 0], -18), ([0, -2, 0, 2, -1, 1, 0], -36), ([0, -1, -1, 1, -1, 1, 1], -27), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 0, -1, 2, 0], -27), ([0, -1, 0, 1, -2, 2, 0], -27), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 2, -2, 1, 0], -27), ([0, -1, 0, 2, -1, 0, 0], -27), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -1, 1, -1], -27), ([1, -2, 0, 1, 0, 1, 0], -18), ([1, -1, -1, 1, -1, 1, 1], -27)]

def combined52_part1 : Sparse := [([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 2, 0], -27), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 2, -1, 0, 0], -27), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 1, -2, 1, 0], -36), ([1, 0, 0, 1, -1, 0, 0], 9)]

def combined52 : Sparse := combined52_part0 ++ combined52_part1

def combined53_part0 : Sparse := [([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 1, -1, 2, 0], -27), ([0, -2, 0, 1, 0, 1, 0], -9), ([0, -2, 0, 2, -1, 1, 0], -36), ([0, -2, 1, 1, -1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], -18), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, -1, 2, 0], -27), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -2, 2, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 0, 2, -2, 1, 0], -27), ([0, -1, 0, 2, -1, 0, 0], -9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, 0, -1, 1, -1, 1, 0], -27)]

def combined53_part1 : Sparse := [([0, 0, 0, 1, -2, 1, 0], -27), ([0, 0, 0, 1, -1, 1, -1], -18), ([1, -2, 0, 1, 0, 1, 0], -9), ([1, -2, 1, 1, -1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], -18), ([1, -1, -1, 1, -1, 2, 0], 18), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 2, 0], -27), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 1, -2, 1, 1], 18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, -1, 2, -1], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, -1, 0, 0], -9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 0, 0, 1, -2, 1, 0], -27), ([1, 0, 0, 1, -1, 0, 0], 9)]

def combined54_part0 : Sparse := [([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 1, -1, 2, 0], -18), ([0, -2, 0, 1, 0, 1, 0], -9), ([0, -2, 0, 2, -1, 1, 0], -27), ([0, -2, 1, 1, -1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], -9), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 2, 0], -18), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -2, 2, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 2, -2, 1, 0], -27), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, 0, -1, 1, -1, 1, 0], -27), ([0, 0, 0, 1, -2, 1, 0], -9), ([0, 0, 0, 1, -1, 1, -1], -18), ([1, -2, 0, 1, -1, 1, 1], 9), ([1, -2, 0, 1, 0, 1, 0], -9), ([1, -2, 1, 1, -1, 1, 0], 18)]

def combined54_part1 : Sparse := [([1, -1, -1, 1, -1, 1, 1], -9), ([1, -1, -1, 1, -1, 2, 0], 18), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 2, -1, 1, 0], 9), ([1, -1, 0, 0, -1, 2, 0], -18), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, -1, 0, 1, -2, 1, 1], 18), ([1, -1, 0, 1, -1, 2, -1], 18), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 0, 0, 1, -2, 1, 0], -9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 1, -1], 9)]

def combined54 : Sparse := combined54_part0 ++ combined54_part1

def combined55 : Sparse := [([0, -2, 0, 1, -1, 2, 0], -18), ([0, -2, 0, 2, -1, 1, 0], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 1, -2, 2, 0], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 2, -2, 1, 0], -18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, 0, -1, 1, -1, 1, 0], -18), ([0, 0, 0, 1, -1, 1, -1], -18), ([1, -2, 0, 1, -1, 1, 1], 18), ([1, -2, 1, 1, -1, 1, 0], 18), ([1, -1, -1, 1, -1, 2, 0], 18), ([1, -1, -1, 2, -1, 1, 0], 18), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, -1, 0, 1, -2, 1, 1], 18), ([1, -1, 0, 1, -1, 2, -1], 18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, -1, 0, 2, -1, 1, -1], 18), ([1, -1, 1, 1, -2, 1, 0], 18), ([1, 0, 0, 0, -1, 1, 0], 18), ([1, 0, 0, 1, -1, 0, 0], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined56_part0 : Sparse := [([0, -2, 0, 1, 0, -1, 2], 36), ([0, -2, 0, 1, 0, 0, 1], -18), ([0, -2, 0, 2, 0, -1, 1], -36), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], -27), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -2, 2], -27), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 9), ([1, -2, 0, 1, 0, -1, 2], 36), ([1, -2, 0, 1, 0, 0, 1], -18), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 2, 0, -1, 1], 9)]

def combined56_part1 : Sparse := [([1, -1, 0, 0, 0, -1, 2], -27), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], -27), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -2, 1], 36), ([1, 0, 0, 1, 0, -1, 0], 9)]

def combined56 : Sparse := combined56_part0 ++ combined56_part1

def combined57_part0 : Sparse := [([0, -2, 0, 1, 0, -1, 2], 27), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -2, 0, 2, 0, -1, 1], -36), ([0, -1, -1, 1, 0, -1, 2], -18), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], -27), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 1, -1, -1, 2], 18), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -2, 2], -18), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([1, -2, 0, 1, 0, -1, 2], 27), ([1, -2, 0, 1, 0, 0, 1], -9)]

def combined57_part1 : Sparse := [([1, -2, 0, 1, 1, -1, 1], -9), ([1, -2, 1, 1, 0, -1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], -9), ([1, -1, -1, 1, 0, 0, 1], 27), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], -27), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], -27), ([1, -1, 0, 2, 0, -1, 0], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -2, 1], 27), ([1, 0, 0, 1, 0, -1, 0], 9)]

def combined57 : Sparse := combined57_part0 ++ combined57_part1

def combined58_part0 : Sparse := [([0, -2, 0, 1, 0, -1, 2], 18), ([0, -2, 0, 1, 0, 0, 1], -9), ([0, -2, 0, 1, 1, -1, 1], -9), ([0, -2, 0, 2, 0, -1, 1], -27), ([0, -2, 1, 1, 0, -1, 1], 9), ([0, -1, -1, 1, 0, -1, 2], -18), ([0, -1, -1, 1, 0, 0, 1], 27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 1, -1, -1, 2], 18), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 0, 1, 0, -2, 2], -18), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, 0, -1, 1, 0, -1, 1], -27), ([0, 0, 0, 0, 0, -1, 1], 18), ([0, 0, 0, 1, -1, -1, 1], -9), ([1, -2, 0, 1, 0, -1, 2], 18)]

def combined58_part1 : Sparse := [([1, -2, 0, 1, 0, 0, 1], -9), ([1, -2, 0, 1, 1, -1, 1], -18), ([1, -2, 1, 1, 0, -1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, 0, 0, 0, -1, 2], -18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], -27), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, 0, 1, -1, -1, 1], -27), ([1, 0, 0, 1, 0, -2, 1], 9), ([1, 0, 0, 1, 0, -1, 0], 9)]

def combined58 : Sparse := combined58_part0 ++ combined58_part1

def combined59_part0 : Sparse := [([0, -2, 0, 1, 0, -1, 2], 18), ([0, -2, 0, 1, 1, -1, 1], -18), ([0, -2, 0, 2, 0, -1, 1], -18), ([0, -2, 1, 1, 0, -1, 1], 18), ([0, -1, -1, 1, 0, -1, 2], -18), ([0, -1, -1, 1, 0, 0, 1], 18), ([0, -1, -1, 2, 0, -1, 1], 18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 1, -1, -1, 2], 18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 0, 1, 0, -2, 2], -18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 0, 1, 1, -2, 1], 18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, 0, -1, 1, 0, -1, 1], -18), ([0, 0, 0, 0, 0, -1, 1], 18), ([1, -2, 0, 1, 0, -1, 2], 18), ([1, -2, 0, 1, 1, -1, 1], -18), ([1, -1, -1, 1, 0, -1, 2], -18), ([1, -1, -1, 1, 0, 0, 1], 18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18)]

def combined59_part1 : Sparse := [([1, -1, 0, 2, -1, -1, 1], 18), ([1, -1, 0, 2, 0, -2, 1], -18), ([1, -1, 1, 1, 0, -2, 1], 18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, 0, 0, 1, -1, -1, 1], -18), ([1, 0, 0, 1, 0, -1, 0], 18)]

def combined59 : Sparse := combined59_part0 ++ combined59_part1

def combined60_part0 : Sparse := [([0, -2, 0, 1, 0, 1, 0], -18), ([0, -2, 0, 1, 0, 2, -1], 36), ([0, -2, 0, 2, 0, 1, -1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 2, -1], -27), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 1, 0, 2, -2], -27), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 0, 1, -2], 9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 1, -1, 1, -1], -27), ([1, -2, 0, 1, 0, 1, 0], -18), ([1, -2, 0, 1, 0, 2, -1], 36), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 0, 1, -1], 9)]

def combined60_part1 : Sparse := [([1, -1, 0, 0, 0, 2, -1], -27), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 1, 1, 1, -2], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 0, 2, 0, 1, -2], -27), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 0, 1, -2], 36)]

def combined60 : Sparse := combined60_part0 ++ combined60_part1

def combined61_part0 : Sparse := [([0, -2, 0, 1, 0, 1, 0], -9), ([0, -2, 0, 1, 0, 2, -1], 27), ([0, -2, 0, 2, 0, 1, -1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, -1, 1, 0, 2, -1], 18), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 0, 2, -1], -27), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, -1, 2, -1], -18), ([0, -1, 0, 1, 0, 2, -2], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 0, 1, 1, 1, -2], -9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 0, 1, -2], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -27), ([1, -2, 0, 1, 0, 1, 0], -9), ([1, -2, 0, 1, 0, 2, -1], 27)]

def combined61_part1 : Sparse := [([1, -2, 0, 1, 1, 1, -1], -9), ([1, -2, 1, 1, 0, 1, -1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 0, 2, -1], -27), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, -1, 2, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 1, 1, 1, -2], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 0, 2, 0, 1, -2], -27), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, 0, -1, 1, 0, 1, -1], -27), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 0, 1, -2], 27)]

def combined61 : Sparse := combined61_part0 ++ combined61_part1

def combined62_part0 : Sparse := [([0, -2, 0, 1, 0, 2, -1], 27), ([0, -2, 0, 1, 1, 1, -1], 9), ([0, -2, 0, 2, 0, 1, -1], -27), ([0, -2, 1, 1, 0, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], -27), ([0, -1, -1, 1, 0, 2, -1], 18), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 0, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 0, 1, -1, 2, -1], -18), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 0, 2, -2], -18), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 0, 2, -1, 1, -1], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 1, 0, 1, -2], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([1, -2, 0, 1, 0, 2, -1], 27), ([1, -2, 1, 1, 0, 1, -1], -9)]

def combined62_part1 : Sparse := [([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 2, 0, 1, -1], 18), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 0, 2, -1], -9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 0, 1, -1, 2, -1], -9), ([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 0, 1, 1, 1, -2], 18), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 0, 2, 0, 1, -2], -18), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], 18), ([1, 0, 0, 1, 0, 1, -2], 18)]

def combined62 : Sparse := combined62_part0 ++ combined62_part1

def combined63_part0 : Sparse := [([0, -2, 0, 1, 0, 2, -1], 18), ([0, -2, 0, 1, 1, 1, -1], 18), ([0, -2, 0, 2, 0, 1, -1], -18), ([0, -2, 1, 1, 0, 1, -1], -18), ([0, -1, -1, 1, 0, 1, 0], -18), ([0, -1, -1, 1, 0, 2, -1], 18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 0, 1, -1, 2, -1], -18), ([0, -1, 0, 1, 0, 0, 0], 18), ([0, -1, 0, 1, 0, 2, -2], -18), ([0, -1, 0, 2, -1, 1, -1], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 1, 0, 1, -2], 18), ([0, 0, 0, 0, 0, 1, -1], 18), ([0, 0, 0, 1, -1, 1, -1], -18), ([1, -2, 0, 1, 0, 2, -1], 18), ([1, -2, 1, 1, 0, 1, -1], -18), ([1, -1, -1, 2, 0, 1, -1], 18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 0, 1, -1, 2, -1], -18)]

def combined63_part1 : Sparse := [([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 0, 1, 1, 1, -2], 18), ([1, -1, 0, 2, 0, 1, -2], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, 0, -1, 1, 0, 1, -1], -18), ([1, 0, 0, 1, 0, 0, -1], 18)]

def combined63 : Sparse := combined63_part0 ++ combined63_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined64_part0 : Sparse := [([0, -2, 0, 1, 2, -1, 0], -36), ([0, -1, -1, 1, 1, -1, 1], -27), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 0, 1, 2, -2, 0], 27), ([0, -1, 0, 2, 1, -2, 0], -27), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], -36), ([0, 0, 0, 1, 1, -1, -1], -27), ([1, -2, 0, 1, 1, 0, 0], 18), ([1, -2, 0, 2, 1, -1, 0], -36), ([1, -1, -1, 1, 1, -1, 1], -27), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], 27)]

def combined64_part1 : Sparse := [([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 1, 2, -2, 0], 27), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, -1, 0], 27), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, 0, -1, 1, 1, -1, 0], 27), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 1, 1, -2, 0], -36)]

def combined64 : Sparse := combined64_part0 ++ combined64_part1

def combined65_part0 : Sparse := [([0, -2, 0, 1, 2, -1, 0], -27), ([0, -2, 1, 1, 1, -1, 0], -9), ([0, -1, -1, 1, 1, -1, 1], -18), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 1, 2, -1, 0], -9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 2, -1, 0], -27), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 0, 1, 2, -2, 0], 18), ([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 0, 2, 1, -2, 0], -27), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, 0, -1, 1, 1, -1, 0], 27), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], -27), ([0, 0, 0, 1, 1, -1, -1], -27), ([1, -2, 0, 1, 1, -1, 1], -9)]

def combined65_part1 : Sparse := [([1, -2, 0, 1, 1, 0, 0], 9), ([1, -2, 0, 2, 1, -1, 0], -36), ([1, -1, -1, 1, 1, -1, 1], -18), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 2, -1, 0], -18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 0, 2, -1, 0], -27), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -18), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 0, 1, 2, -2, 0], 18), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, -1, 0], 9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], -18), ([1, 0, 0, 1, 1, -2, 0], -27), ([1, 0, 0, 1, 1, -1, -1], -9)]

def combined65 : Sparse := combined65_part0 ++ combined65_part1

def combined66_part0 : Sparse := [([0, -2, 0, 1, 1, -1, 1], 9), ([0, -2, 0, 1, 2, -1, 0], -27), ([0, -1, -1, 1, 1, -1, 1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, -1, 0], -9), ([0, -1, -1, 2, 1, -1, 0], 9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 2, -1, 0], -9), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 0, 1, 1, -2, 1], -18), ([0, -1, 0, 1, 2, -2, 0], 18), ([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 0, 2, 1, -2, 0], -18), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 1, -2, 0], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 0, 1, 1, -2, 0], -18), ([0, 0, 0, 1, 1, -1, -1], -18), ([1, -2, 0, 2, 1, -1, 0], -27)]

def combined66_part1 : Sparse := [([1, -2, 1, 1, 1, -1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], -9), ([1, -1, -1, 1, 2, -1, 0], -18), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 0, 2, -1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 1, -2, 1], -18), ([1, -1, 0, 1, 1, 0, -1], -27), ([1, -1, 0, 1, 2, -2, 0], 18), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, -1, 0], 9), ([1, -1, 0, 2, 1, -1, -1], 9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], -18), ([1, 0, 0, 1, 1, -2, 0], -18)]

def combined66 : Sparse := combined66_part0 ++ combined66_part1

def combined67_part0 : Sparse := [([0, -2, 0, 1, 1, -1, 1], 18), ([0, -2, 0, 1, 2, -1, 0], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, -1, 1, 2, -1, 0], -18), ([0, -1, -1, 2, 1, -1, 0], 18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 1, 0, 0], 18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 0, 1, 1, -2, 1], -18), ([0, -1, 0, 1, 2, -2, 0], 18), ([0, -1, 0, 1, 2, -1, -1], 18), ([0, -1, 0, 2, 1, -2, 0], -18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, 1, -2, 0], 18), ([0, 0, -1, 1, 1, -1, 0], 18), ([0, 0, 0, 0, 1, -1, 0], -18), ([0, 0, 0, 1, 0, -1, 0], 18), ([0, 0, 0, 1, 1, -1, -1], -18), ([1, -2, 0, 2, 1, -1, 0], -18), ([1, -2, 1, 1, 1, -1, 0], 18), ([1, -1, -1, 1, 2, -1, 0], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 1, 0, 0, 0], 18), ([1, -1, 0, 1, 1, -2, 1], -18)]

def combined67_part1 : Sparse := [([1, -1, 0, 1, 1, 0, -1], -18), ([1, -1, 0, 1, 2, -2, 0], 18), ([1, -1, 0, 2, 1, -1, -1], 18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, 0, -1, 1, 1, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], -18)]

def combined67 : Sparse := combined67_part0 ++ combined67_part1

def combined68_part0 : Sparse := [([0, -2, 0, 1, 2, 0, -1], -36), ([0, -2, 0, 2, 1, 0, -1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 0, 1, 1, 1, -2], -9), ([0, -1, 0, 1, 2, 0, -2], -27), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 0, 2, 1, 0, -2], -27), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 1, 1, 0, -2], -9), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -27), ([1, -2, 0, 1, 1, 0, 0], 18), ([1, -1, -1, 1, 1, 1, -1], 27), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 0, 1, -1], 9)]

def combined68_part1 : Sparse := [([1, -1, 0, 1, 1, 1, -2], -9), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], 27), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 27), ([1, -1, 1, 1, 1, 0, -2], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 1, 0, -2], 36)]

def combined68 : Sparse := combined68_part0 ++ combined68_part1

def combined69_part0 : Sparse := [([0, -2, 0, 1, 2, 0, -1], -27), ([0, -2, 0, 2, 1, 0, -1], -36), ([0, -2, 1, 1, 1, 0, -1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, 0, -1], -18), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 0, 1, 1, 1, -2], -18), ([0, -1, 0, 1, 2, -1, -1], -9), ([0, -1, 0, 1, 2, 0, -2], -18), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 0, 2, 1, 0, -2], -27), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 1, 1, 0, -2], -9), ([0, 0, -1, 1, 1, 0, -1], -27), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], -18), ([1, -2, 0, 1, 1, 0, 0], 9), ([1, -2, 0, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 1, 0, 0], 9)]

def combined69_part1 : Sparse := [([1, -1, -1, 1, 1, 1, -1], 18), ([1, -1, -1, 1, 2, 0, -1], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 0, 2, 0, -1], 27), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 1, 1, -2], -9), ([1, -1, 0, 1, 2, -1, -1], -18), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 18), ([1, -1, 1, 1, 1, 0, -2], -18), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 0, 1, 1, 0, -2], 27)]

def combined69 : Sparse := combined69_part0 ++ combined69_part1

def combined70_part0 : Sparse := [([0, -2, 0, 1, 1, 1, -1], -9), ([0, -2, 0, 1, 2, 0, -1], -27), ([0, -2, 0, 2, 1, 0, -1], -27), ([0, -2, 1, 1, 1, 0, -1], -9), ([0, -1, -1, 1, 1, 0, 0], -27), ([0, -1, -1, 1, 2, 0, -1], -18), ([0, -1, -1, 2, 1, 0, -1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 1, 1, -1, 0], -27), ([0, -1, 0, 1, 1, 1, -2], -18), ([0, -1, 0, 1, 2, -1, -1], -9), ([0, -1, 0, 1, 2, 0, -2], -18), ([0, -1, 0, 2, 1, -1, -1], -18), ([0, -1, 0, 2, 1, 0, -2], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 1, 1, 1, 0, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18)]

def combined70_part1 : Sparse := [([1, -2, 0, 1, 1, 1, -1], -9), ([1, -2, 1, 1, 1, 0, -1], -9), ([1, -1, -1, 1, 1, 1, -1], 9), ([1, -1, -1, 1, 2, 0, -1], -9), ([1, -1, -1, 2, 1, 0, -1], -18), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 0, 2, 0, -1], 9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 1, 1, 1, -2], -18), ([1, -1, 0, 1, 2, -1, -1], -18), ([1, -1, 0, 2, 0, 0, -1], 9), ([1, -1, 0, 2, 1, -1, -1], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], 9), ([1, -1, 1, 1, 1, 0, -2], -18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18), ([1, 0, 0, 1, 1, 0, -2], 18)]

def combined70 : Sparse := combined70_part0 ++ combined70_part1

def combined71_part0 : Sparse := [([0, -2, 0, 1, 1, 1, -1], -18), ([0, -2, 0, 1, 2, 0, -1], -18), ([0, -2, 0, 2, 1, 0, -1], -18), ([0, -2, 1, 1, 1, 0, -1], -18), ([0, -1, -1, 1, 1, 0, 0], -18), ([0, -1, -1, 1, 2, 0, -1], -18), ([0, -1, -1, 2, 1, 0, -1], -18), ([0, -1, 0, 0, 1, 0, 0], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 0, 0, 0], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 0, 1, 1, -1, 0], -18), ([0, -1, 0, 1, 1, 1, -2], -18), ([0, -1, 0, 1, 2, -1, -1], -18), ([0, -1, 0, 1, 2, 0, -2], -18), ([0, -1, 0, 2, 1, -1, -1], -18), ([0, -1, 0, 2, 1, 0, -2], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 1, 1, 1, 0, -2], -18), ([0, 0, -1, 1, 1, 0, -1], -18), ([0, 0, 0, 0, 1, 0, -1], -18), ([0, 0, 0, 1, 0, 0, -1], -18), ([0, 0, 0, 1, 1, -1, -1], -18)]

def combined71_part1 : Sparse := [([1, -2, 0, 1, 1, 1, -1], -18), ([1, -2, 1, 1, 1, 0, -1], -18), ([1, -1, -1, 1, 2, 0, -1], -18), ([1, -1, -1, 2, 1, 0, -1], -18), ([1, -1, 0, 0, 1, 0, 0], -18), ([1, -1, 0, 1, 0, 0, 0], -18), ([1, -1, 0, 1, 1, 1, -2], -18), ([1, -1, 0, 1, 2, -1, -1], -18), ([1, -1, 0, 2, 1, -1, -1], -18), ([1, -1, 1, 1, 1, 0, -2], -18), ([1, 0, 0, 0, 1, 0, -1], -18), ([1, 0, 0, 1, 0, 0, -1], -18)]

def combined71 : Sparse := combined71_part0 ++ combined71_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined72_part0 : Sparse := [([0, -2, 2, -1, 0, 0, 1], -36), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 1, -2, 0, 0, 2], -27), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 2, -2, 0, 0, 1], 27), ([0, -1, 2, -1, 0, 0, 0], -27), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 1, -2, 0, 0, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, -1, 0, 0, 2], -36), ([1, -2, 1, 0, 0, 0, 1], 18), ([1, -1, 0, -1, 0, 0, 2], 27), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 1, -2, 1, 0, 1], -9)]

def combined72_part1 : Sparse := [([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 2, -2, 0, 0, 1], 27), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, -1, 0, 0, 0], -27), ([1, 0, 1, -2, 0, 0, 1], -36), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, -1, 0, 0, 0], -9)]

def combined72 : Sparse := combined72_part0 ++ combined72_part1

def combined73_part0 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 1, 0, 1], 9), ([0, -2, 2, -1, 0, 0, 1], -36), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 1, -2, 0, 0, 2], -18), ([0, -1, 1, -2, 0, 1, 1], 18), ([0, -1, 1, -2, 1, 0, 1], -18), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 0, -1, 2], 9), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 2, -2, 0, 0, 1], 27), ([0, -1, 2, -1, 0, 0, 0], -9), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 1, -2, 0, 0, 1], -27), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, -1, 0, 0, 2], -27), ([1, -2, 1, -1, 0, 1, 1], 9)]

def combined73_part1 : Sparse := [([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, 0, 0, 0, 1], 9), ([1, -1, 0, -1, 0, 0, 2], 27), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, -1, 0, 2], 9), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 2, -2, 0, 0, 1], 27), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, -1, 0, 0, 0], -9), ([1, 0, 1, -2, 0, 0, 1], -27), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, -1, 0, 0, 0], -9)]

def combined73 : Sparse := combined73_part0 ++ combined73_part1

def combined74_part0 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 1, 0, 1], 18), ([0, -2, 2, -1, 0, 0, 1], -27), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 1, -2, 0, 0, 2], -18), ([0, -1, 1, -2, 0, 1, 1], 18), ([0, -1, 1, -2, 1, 0, 1], -18), ([0, -1, 1, -1, 0, -1, 2], 18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 2, -2, 0, 0, 1], 27), ([0, -1, 2, -1, -1, 0, 1], 9), ([0, -1, 2, -1, 0, -1, 1], -9), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 1, -2, 0, 0, 1], -9), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, -1, 0, 0, 2], -18), ([1, -2, 1, -1, 0, 1, 1], 18)]

def combined74_part1 : Sparse := [([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, 0, 0, 0, 1], 9), ([1, -1, 0, -1, 0, 0, 2], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, -1, 0, 2], 18), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 2, -2, 0, 0, 1], 27), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], -9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, -1, 0, 0, 0], -9)]

def combined74 : Sparse := combined74_part0 ++ combined74_part1

def combined75_part0 : Sparse := [([0, -2, 1, -1, 1, 0, 1], 18), ([0, -2, 2, -1, 0, 0, 1], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 1, -2, 0, 0, 2], -18), ([0, -1, 1, -2, 0, 1, 1], 18), ([0, -1, 1, -2, 1, 0, 1], -18), ([0, -1, 1, -1, 0, -1, 2], 18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 2, -2, 0, 0, 1], 18), ([0, -1, 2, -1, -1, 0, 1], 18), ([0, -1, 2, -1, 0, -1, 1], -18), ([0, 0, 0, -1, 0, 0, 1], 18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, -1, 0, 0, 0], -18), ([1, -2, 1, -1, 0, 0, 2], -18), ([1, -2, 1, -1, 0, 1, 1], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, 0, 0, 0, 1], 18), ([1, -1, 1, -2, 1, 0, 1], -18), ([1, -1, 1, -1, -1, 0, 2], 18)]

def combined75_part1 : Sparse := [([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 2, -2, 0, 0, 1], 18), ([1, -1, 2, -1, 0, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, -1, 0, 0, 0], -18)]

def combined75 : Sparse := combined75_part0 ++ combined75_part1

def combined76_part0 : Sparse := [([0, -2, 1, -1, 0, 2, 0], -36), ([0, -2, 1, 0, 0, 1, 0], -18), ([0, -2, 2, -1, 0, 1, 0], 36), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 2, -2, 0, 1, 0], -27), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 0, 0], -27), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], -27), ([1, -2, 1, 0, 0, 1, 0], -18), ([1, -2, 2, -1, 0, 1, 0], 36), ([1, -1, 0, -1, 0, 1, 1], -27), ([1, -1, 0, -1, 0, 2, 0], 27), ([1, -1, 0, -1, 1, 1, 0], 9)]

def combined76_part1 : Sparse := [([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 0, 2, 0], -27), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, -1, 0, 0, 0], -27), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 1, -2, 0, 1, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -27)]

def combined76 : Sparse := combined76_part0 ++ combined76_part1

def combined77_part0 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 0, 2, 0], -27), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 1, 0, 0, 1, 0], -9), ([0, -2, 2, -1, 0, 1, 0], 36), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 1, 0], 18), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 0, 2, -1], 18), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 2, -2, 0, 1, 0], -27), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 0, 0], -9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], -18)]

def combined77_part1 : Sparse := [([1, -2, 1, -1, 0, 1, 1], 9), ([1, -2, 1, 0, 0, 1, 0], -9), ([1, -2, 2, -1, 0, 1, 0], 36), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, -1, 0, 2, 0], 27), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 1, -2, 0, 1, 1], 18), ([1, -1, 1, -2, 0, 2, 0], -18), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, -1, -1, 2, 0], 18), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, -1, 0, 0, 0], -9), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 0, 1, -2, 0, 1, 0], 27), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, 0, 1, -1], 9)]

def combined77 : Sparse := combined77_part0 ++ combined77_part1

def combined78_part0 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 18), ([0, -2, 1, -1, 0, 2, 0], -18), ([0, -2, 1, -1, 1, 1, 0], -18), ([0, -2, 1, 0, 0, 1, 0], -9), ([0, -2, 2, -1, 0, 1, 0], 27), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 1, 0], 18), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 0, 2, -1], 18), ([0, -1, 1, -1, 1, 0, 0], 27), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 2, -2, 0, 1, 0], -27), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], -18), ([1, -2, 1, -1, 0, 1, 1], 9), ([1, -2, 1, -1, 1, 1, 0], -9)]

def combined78_part1 : Sparse := [([1, -2, 1, 0, 0, 1, 0], -9), ([1, -2, 2, -1, 0, 1, 0], 27), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 0, -1, 0, 2, 0], 18), ([1, -1, 1, -2, 0, 1, 1], 18), ([1, -1, 1, -2, 0, 2, 0], -18), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, -1, -1, 2, 0], 18), ([1, -1, 1, -1, 1, 0, 0], 27), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 0, 1, -2, 0, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, -1, 0, 1, -1], 9)]

def combined78 : Sparse := combined78_part0 ++ combined78_part1

def combined79_part0 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 18), ([0, -2, 1, -1, 0, 2, 0], -18), ([0, -2, 1, -1, 1, 1, 0], -18), ([0, -2, 2, -1, 0, 1, 0], 18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, 0, 0, 1, 0], 18), ([0, -1, 1, -2, 1, 1, 0], 18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, -1, 0, 2, -1], 18), ([0, -1, 1, -1, 1, 0, 0], 18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 2, -2, 0, 1, 0], -18), ([0, -1, 2, -1, -1, 1, 0], 18), ([0, -1, 2, -1, 0, 1, -1], -18), ([0, 0, 1, -1, 0, 0, 0], 18), ([0, 0, 1, -1, 0, 1, -1], -18), ([1, -2, 1, -1, 1, 1, 0], -18), ([1, -2, 2, -1, 0, 1, 0], 18), ([1, -1, 0, -1, 0, 1, 1], -18), ([1, -1, 1, -2, 0, 1, 1], 18), ([1, -1, 1, -2, 0, 2, 0], -18), ([1, -1, 1, -1, -1, 2, 0], 18)]

def combined79_part1 : Sparse := [([1, -1, 1, -1, 1, 0, 0], 18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 2, -1, 0, 1, -1], -18), ([1, 0, 0, -1, 0, 1, 0], 18), ([1, 0, 1, -1, -1, 1, 0], -18)]

def combined79 : Sparse := combined79_part0 ++ combined79_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined80_part0 : Sparse := [([0, -2, 1, -1, 2, 0, 0], -36), ([0, -2, 1, 0, 1, 0, 0], -18), ([0, -2, 2, -1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 0, 1], -27), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, -1, 2, 0, 0], -27), ([0, -1, 1, -2, 2, 0, 0], -27), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 2, -2, 1, 0, 0], -27), ([0, -1, 2, -1, 0, 0, 0], -27), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, 0, 1, -2, 1, 0, 0], -36), ([0, 0, 1, -1, 1, -1, 0], -27), ([0, 0, 1, -1, 1, 0, -1], -27), ([1, -2, 1, 0, 1, 0, 0], -18), ([1, -1, 0, -1, 1, 0, 1], 9)]

def combined80_part1 : Sparse := [([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, 0, 0], -27), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 2, -1, 0, 0, 0], -27), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 1, -2, 1, 0, 0], -36), ([1, 0, 1, -1, 0, 0, 0], 9)]

def combined80 : Sparse := combined80_part0 ++ combined80_part1

def combined81_part0 : Sparse := [([0, -2, 1, -1, 1, 0, 1], 9), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 1, -1, 2, 0, 0], -27), ([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 2, -1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 1, 0], -27), ([0, -1, 0, -1, 2, 0, 0], -27), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -2, 2, 0, 0], -18), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 2, -2, 1, 0, 0], -27), ([0, -1, 2, -1, 0, 0, 0], -9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, 0, 1, -2, 1, 0, 0], -27)]

def combined81_part1 : Sparse := [([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, -1, 1, 0, -1], -27), ([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, 0, 1, 0, 0], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, 0, 0], -27), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -2, 1, 1, 0], 18), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, -1, 2, -1, 0], 9), ([1, -1, 1, -1, 2, 0, -1], 18), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 2, -1, 0, 0, 0], -9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 0, 1, -2, 1, 0, 0], -27), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], 9)]

def combined81_part2 : Sparse := [([1, 0, 1, -1, 1, 0, -1], -9)]

def combined81 : Sparse := combined81_part0 ++ combined81_part1 ++ combined81_part2

def combined82_part0 : Sparse := [([0, -2, 1, -1, 1, 0, 1], 9), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 1, -1, 2, 0, 0], -18), ([0, -2, 1, 0, 1, 0, 0], -9), ([0, -2, 2, -1, 1, 0, 0], -27), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 0, -1, 2, 0, 0], -18), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -2, 2, 0, 0], -18), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 2, -2, 1, 0, 0], -27), ([0, 0, 1, -2, 1, 0, 0], -9), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, -1, 1, 0, -1], -27), ([1, -2, 1, -1, 1, 0, 1], 18), ([1, -2, 1, -1, 1, 1, 0], 9), ([1, -2, 1, 0, 1, 0, 0], -9)]

def combined82_part1 : Sparse := [([1, -1, 0, -1, 2, 0, 0], -18), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -2, 1, 1, 0], 18), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, -1, 2, -1, 0], 18), ([1, -1, 1, -1, 2, 0, -1], 18), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 0, 1, -2, 1, 0, 0], -9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, -1, 1, 0, -1], -9)]

def combined82 : Sparse := combined82_part0 ++ combined82_part1

def combined83 : Sparse := [([0, -2, 1, -1, 2, 0, 0], -18), ([0, -2, 2, -1, 1, 0, 0], -18), ([0, -1, 0, -1, 1, 0, 1], -18), ([0, -1, 0, -1, 1, 1, 0], -18), ([0, -1, 1, -2, 2, 0, 0], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 2, -2, 1, 0, 0], -18), ([0, 0, 1, -1, 1, -1, 0], -18), ([0, 0, 1, -1, 1, 0, -1], -18), ([1, -2, 1, -1, 1, 0, 1], 18), ([1, -2, 1, -1, 1, 1, 0], 18), ([1, -1, 0, 0, 1, 0, 0], 18), ([1, -1, 1, -2, 1, 0, 1], 18), ([1, -1, 1, -2, 1, 1, 0], 18), ([1, -1, 1, -1, 2, -1, 0], 18), ([1, -1, 1, -1, 2, 0, -1], 18), ([1, -1, 1, 0, 0, 0, 0], 18), ([1, -1, 2, -1, 1, -1, 0], 18), ([1, -1, 2, -1, 1, 0, -1], 18), ([1, 0, 0, -1, 1, 0, 0], 18), ([1, 0, 1, -1, 0, 0, 0], 18)]

def combined84_part0 : Sparse := [([0, -2, 1, 0, -1, 0, 2], -36), ([0, -2, 2, 0, -1, 0, 1], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 1, -1, 0, 1], -27), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, 0, -2, 0, 2], -27), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 2, 0, -2, 0, 1], -27), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, -1, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], 18), ([1, -1, 0, 0, -1, 0, 2], 27), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, 0, -2, 1, 1], -9)]

def combined84_part1 : Sparse := [([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, 0, 0], 27), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, 0, -2, 0, 1], 36), ([1, 0, 1, 0, -1, 0, 0], -9)]

def combined84 : Sparse := combined84_part0 ++ combined84_part1

def combined85_part0 : Sparse := [([0, -2, 1, 0, -1, 0, 2], -27), ([0, -2, 1, 1, -1, 0, 1], -9), ([0, -2, 2, 0, -1, 0, 1], -36), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 1, -1, -1, 0, 2], -18), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, 0, -2, 0, 2], -18), ([0, -1, 1, 0, -2, 1, 1], -18), ([0, -1, 1, 0, -1, -1, 2], -9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 2, 0, -2, 0, 1], -27), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, -1, 0, 0], -9), ([1, -2, 1, 0, -1, 1, 1], -9), ([1, -2, 1, 0, 0, 0, 1], 9), ([1, -1, 0, 0, -1, 0, 2], 27)]

def combined85_part1 : Sparse := [([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 1, -1, -1, 0, 2], -9), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, -1, 1, 0, -1, -1, 2], -18), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 1, -2, 0, 1], -18), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, 0, -2, 0, 1], 27), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, 0, 0], -9)]

def combined85 : Sparse := combined85_part0 ++ combined85_part1

def combined86_part0 : Sparse := [([0, -2, 1, 0, -1, 0, 2], -18), ([0, -2, 1, 0, -1, 1, 1], -9), ([0, -2, 1, 1, -1, 0, 1], -18), ([0, -2, 2, 0, -1, 0, 1], -27), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 1, -1, -1, 0, 2], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, 0, -2, 0, 2], -18), ([0, -1, 1, 0, -2, 1, 1], -18), ([0, -1, 1, 0, -1, -1, 2], -18), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, 0, -1, 1], -27), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 2, -1, -1, 0, 1], -9), ([0, -1, 2, 0, -2, 0, 1], -27), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 1, -1, -1, 0, 1], -27), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, -1, 0, 0], -9)]

def combined86_part1 : Sparse := [([1, -2, 1, 0, -1, 1, 1], -18), ([1, -2, 1, 0, 0, 0, 1], 9), ([1, -2, 1, 1, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], 18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 1, -1, -1, 0, 2], -18), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, -1, 1, 0, -1, -1, 2], -18), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 1, -2, 0, 1], -18), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, -1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, 0, -2, 0, 1], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, 0, 0], -9)]

def combined86 : Sparse := combined86_part0 ++ combined86_part1

def combined87_part0 : Sparse := [([0, -2, 1, 0, -1, 0, 2], -18), ([0, -2, 1, 0, -1, 1, 1], -18), ([0, -2, 1, 1, -1, 0, 1], -18), ([0, -2, 2, 0, -1, 0, 1], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 0, 1], -18), ([0, -1, 0, 1, -1, 0, 1], -18), ([0, -1, 1, -1, -1, 0, 2], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, 0, -2, 0, 2], -18), ([0, -1, 1, 0, -2, 1, 1], -18), ([0, -1, 1, 0, -1, -1, 2], -18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 0, 0, -1, 1], -18), ([0, -1, 1, 0, 0, 0, 0], -18), ([0, -1, 1, 1, -2, 0, 1], -18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 2, -1, -1, 0, 1], -18), ([0, -1, 2, 0, -2, 0, 1], -18), ([0, -1, 2, 0, -1, -1, 1], -18), ([0, 0, 0, 0, -1, 0, 1], -18), ([0, 0, 1, -1, -1, 0, 1], -18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, -1, 0, 0], -18)]

def combined87_part1 : Sparse := [([1, -2, 1, 0, -1, 1, 1], -18), ([1, -2, 1, 1, -1, 0, 1], -18), ([1, -1, 0, 0, 0, 0, 1], -18), ([1, -1, 1, -1, -1, 0, 2], -18), ([1, -1, 1, 0, -2, 1, 1], -18), ([1, -1, 1, 0, -1, -1, 2], -18), ([1, -1, 1, 0, 0, 0, 0], -18), ([1, -1, 1, 1, -2, 0, 1], -18), ([1, -1, 2, -1, -1, 0, 1], -18), ([1, -1, 2, 0, -1, -1, 1], -18), ([1, 0, 0, 0, -1, 0, 1], -18), ([1, 0, 1, 0, -1, 0, 0], -18)]

def combined87 : Sparse := combined87_part0 ++ combined87_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined88_part0 : Sparse := [([0, -2, 1, 0, -1, 2, 0], 36), ([0, -2, 1, 0, 0, 1, 0], -18), ([0, -2, 2, 0, -1, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -27), ([0, -1, 0, 0, -1, 2, 0], -27), ([0, -1, 0, 1, -1, 1, 0], 27), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, 0, -2, 2, 0], -27), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, 0, -1, 1, -1], -27), ([1, -2, 1, 0, -1, 2, 0], 36), ([1, -2, 1, 0, 0, 1, 0], -18), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], -27), ([1, -1, 0, 1, -1, 1, 0], 36)]

def combined88_part1 : Sparse := [([1, -1, 1, -1, -1, 1, 1], 27), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], -27), ([1, -1, 2, 0, -1, 0, 0], 27), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, 0, -2, 1, 0], 36), ([1, 0, 1, 0, -1, 0, 0], 9)]

def combined88 : Sparse := combined88_part0 ++ combined88_part1

def combined89_part0 : Sparse := [([0, -2, 1, 0, -1, 2, 0], 27), ([0, -2, 1, 0, 0, 1, 0], -9), ([0, -2, 2, 0, -1, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 2, 0], -27), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 1, -1, -1, 2, 0], 18), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -2, 2, 0], -18), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 2, -1], -18), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([1, -2, 1, 0, -1, 1, 1], -9), ([1, -2, 1, 0, -1, 2, 0], 27)]

def combined89_part1 : Sparse := [([1, -2, 1, 0, 0, 1, 0], -9), ([1, -2, 1, 1, -1, 1, 0], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], -27), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], 27), ([1, -1, 1, -1, -1, 1, 1], 18), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, -1, 2, -1], -9), ([1, -1, 1, 0, 0, 1, -1], 27), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], -27), ([1, -1, 2, 0, -1, 0, 0], 9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, 0, -2, 1, 0], 27), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], -9)]

def combined89 : Sparse := combined89_part0 ++ combined89_part1

def combined90_part0 : Sparse := [([0, -2, 1, 0, -1, 1, 1], 9), ([0, -2, 1, 0, -1, 2, 0], 18), ([0, -2, 1, 0, 0, 1, 0], -9), ([0, -2, 1, 1, -1, 1, 0], -9), ([0, -2, 2, 0, -1, 1, 0], -27), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, -1, 2, 0], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 1, -1, -1, 2, 0], 18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -2, 2, 0], -18), ([0, -1, 1, 0, -1, 2, -1], -18), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], 27), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], -27), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 1, -1], -27), ([1, -2, 1, 0, -1, 1, 1], -9)]

def combined90_part1 : Sparse := [([1, -2, 1, 0, -1, 2, 0], 18), ([1, -2, 1, 0, 0, 1, 0], -9), ([1, -2, 1, 1, -1, 1, 0], -18), ([1, -1, 0, 0, -1, 2, 0], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 1, -1, -1, 1, 1], 9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, -1, 2, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], -27), ([1, 0, 1, -1, -1, 1, 0], -27), ([1, 0, 1, 0, -2, 1, 0], 9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], -9)]

def combined90 : Sparse := combined90_part0 ++ combined90_part1

def combined91_part0 : Sparse := [([0, -2, 1, 0, -1, 1, 1], 18), ([0, -2, 1, 0, -1, 2, 0], 18), ([0, -2, 1, 1, -1, 1, 0], -18), ([0, -2, 2, 0, -1, 1, 0], -18), ([0, -1, 0, 0, -1, 1, 1], -18), ([0, -1, 0, 0, 0, 1, 0], -18), ([0, -1, 0, 1, -1, 1, 0], 18), ([0, -1, 1, -1, -1, 2, 0], 18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, 0, -2, 2, 0], -18), ([0, -1, 1, 0, -1, 2, -1], -18), ([0, -1, 1, 0, 0, 0, 0], 18), ([0, -1, 1, 0, 0, 1, -1], 18), ([0, -1, 1, 1, -2, 1, 0], 18), ([0, -1, 1, 1, -1, 0, 0], -18), ([0, -1, 2, 0, -1, 1, -1], 18), ([0, 0, 0, 0, -1, 1, 0], 18), ([0, 0, 1, 0, -1, 1, -1], -18), ([1, -2, 1, 0, -1, 2, 0], 18), ([1, -2, 1, 1, -1, 1, 0], -18), ([1, -1, 0, 0, 0, 1, 0], -18), ([1, -1, 0, 1, -1, 1, 0], 18), ([1, -1, 1, 0, -2, 1, 1], 18), ([1, -1, 1, 0, -1, 0, 1], -18)]

def combined91_part1 : Sparse := [([1, -1, 1, 0, -1, 2, -1], -18), ([1, -1, 1, 0, 0, 1, -1], 18), ([1, -1, 2, -1, -1, 1, 0], 18), ([1, -1, 2, 0, -2, 1, 0], -18), ([1, 0, 1, -1, -1, 1, 0], -18), ([1, 0, 1, 0, -1, 0, 0], 18)]

def combined91 : Sparse := combined91_part0 ++ combined91_part1

def combined92_part0 : Sparse := [([0, -2, 1, 0, 0, -1, 2], -36), ([0, -1, 0, 0, 0, -1, 2], -27), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, -1, 1], -27), ([0, -1, 1, 0, 0, -2, 2], 27), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, -1, 2, 0, 0, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, 0, -2, 1], -36), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], 18), ([1, -2, 2, 0, 0, -1, 1], -36), ([1, -1, 0, 0, 0, -1, 2], -27), ([1, -1, 0, 0, 1, -1, 1], 27), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9)]

def combined92_part1 : Sparse := [([1, -1, 1, -1, 1, -1, 1], -27), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, 0, -2, 2], 27), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], 27), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, 0, 0, -1, 0], 27), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], 27), ([1, 0, 1, 0, 0, -2, 1], -36)]

def combined92 : Sparse := combined92_part0 ++ combined92_part1

def combined93_part0 : Sparse := [([0, -2, 1, 0, 0, -1, 2], -27), ([0, -2, 1, 1, 0, -1, 1], -9), ([0, -1, 0, 0, 0, -1, 2], -27), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], 27), ([0, -1, 0, 1, 0, -1, 1], -27), ([0, -1, 1, -1, 0, -1, 2], -9), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, -1, 1], -18), ([0, -1, 1, 0, -1, -1, 2], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, 0, -2, 2], 18), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, -1, 2, 0, 0, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, 0, -2, 1], -27), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], 9)]

def combined93_part1 : Sparse := [([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 2, 0, 0, -1, 1], -36), ([1, -1, 0, 0, 0, -1, 2], -27), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -18), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], -18), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, 0, -2, 2], 18), ([1, -1, 1, 0, 1, -2, 1], -18), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], 18), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, 0, 0, -1, 0], 9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, 0, -2, 1], -27)]

def combined93 : Sparse := combined93_part0 ++ combined93_part1

def combined94_part0 : Sparse := [([0, -2, 1, 0, 0, -1, 2], -18), ([0, -2, 1, 0, 1, -1, 1], 9), ([0, -2, 1, 1, 0, -1, 1], -9), ([0, -1, 0, 0, 0, -1, 2], -18), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 1, -1, 0, -1, 2], -18), ([0, -1, 1, -1, 0, 0, 1], -27), ([0, -1, 1, -1, 1, -1, 1], -9), ([0, -1, 1, 0, -1, -1, 2], 18), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, 0, -2, 2], 18), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 0, 1, -1, 0], -27), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 2, -1, 0, -1, 1], 9), ([0, -1, 2, 0, 0, -2, 1], -27), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 27), ([0, 0, 1, 0, -1, -1, 1], -27), ([0, 0, 1, 0, 0, -2, 1], -9), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], 9)]

def combined94_part1 : Sparse := [([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 1, 0, -1, 1], 9), ([1, -2, 2, 0, 0, -1, 1], -27), ([1, -1, 0, 0, 0, -1, 2], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 1, -1, 0, -1, 2], -18), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], -9), ([1, -1, 1, 0, -1, 0, 1], -27), ([1, -1, 1, 0, 0, -2, 2], 18), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, -2, 1], -18), ([1, -1, 1, 1, -1, -1, 1], 9), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 0, -1, 0], -27), ([1, -1, 2, 0, -1, -1, 1], 9), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, 0, -2, 1], -9)]

def combined94 : Sparse := combined94_part0 ++ combined94_part1

def combined95_part0 : Sparse := [([0, -2, 1, 0, 0, -1, 2], -18), ([0, -2, 1, 0, 1, -1, 1], 18), ([0, -1, 0, 0, 0, 0, 1], 18), ([0, -1, 0, 0, 1, -1, 1], 18), ([0, -1, 0, 1, 0, -1, 1], -18), ([0, -1, 1, -1, 0, -1, 2], -18), ([0, -1, 1, -1, 0, 0, 1], -18), ([0, -1, 1, 0, -1, -1, 2], 18), ([0, -1, 1, 0, 0, -2, 2], 18), ([0, -1, 1, 0, 1, -2, 1], -18), ([0, -1, 1, 0, 1, -1, 0], -18), ([0, -1, 1, 1, 0, -2, 1], 18), ([0, -1, 2, -1, 0, -1, 1], 18), ([0, -1, 2, 0, 0, -2, 1], -18), ([0, 0, 0, 0, 0, -1, 1], -18), ([0, 0, 1, -1, 0, -1, 1], 18), ([0, 0, 1, 0, -1, -1, 1], -18), ([0, 0, 1, 0, 0, -1, 0], 18), ([1, -2, 1, 1, 0, -1, 1], 18), ([1, -2, 2, 0, 0, -1, 1], -18), ([1, -1, 0, 0, 1, -1, 1], 18), ([1, -1, 1, -1, 0, -1, 2], -18), ([1, -1, 1, 0, -1, 0, 1], -18), ([1, -1, 1, 0, 0, -2, 2], 18)]

def combined95_part1 : Sparse := [([1, -1, 1, 0, 0, 0, 0], 18), ([1, -1, 1, 0, 1, -2, 1], -18), ([1, -1, 1, 1, 0, -1, 0], -18), ([1, -1, 2, 0, -1, -1, 1], 18), ([1, 0, 0, 0, 0, -1, 1], -18), ([1, 0, 1, -1, 0, -1, 1], 18)]

def combined95 : Sparse := combined95_part0 ++ combined95_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined96_part0 : Sparse := [([0, -2, 1, 0, 0, 1, 0], -18), ([0, -2, 1, 0, 0, 2, -1], -36), ([0, -2, 2, 0, 0, 1, -1], -36), ([0, -1, 0, 0, 0, 2, -1], -27), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -27), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 1, -1], -27), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 0, 0, 2, -2], -27), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 1, -1, 1, -1], -27), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, -1, 2, 0, 0, 0, -1], -27), ([0, -1, 2, 0, 0, 1, -2], -27), ([0, 0, 1, -1, 0, 1, -1], -27), ([0, 0, 1, 0, -1, 1, -1], -27), ([0, 0, 1, 0, 0, 1, -2], -36), ([1, -2, 1, 0, 0, 1, 0], -18), ([1, -1, 0, 0, 0, 2, -1], -27)]

def combined96_part1 : Sparse := [([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], -27), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 1, -1, 1, -1], -27), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 0, 1, -2], 9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -27), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 0, 1, -2], -36)]

def combined96 : Sparse := combined96_part0 ++ combined96_part1

def combined97_part0 : Sparse := [([0, -2, 1, 0, 0, 1, 0], -9), ([0, -2, 1, 0, 0, 2, -1], -27), ([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 2, 0, 0, 1, -1], -36), ([0, -1, 0, 0, 0, 2, -1], -27), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 1, -1], -18), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 0, 0, 2, -2], -18), ([0, -1, 1, 0, 1, 0, -1], -27), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 1, -1, 1, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 0, 1, -2], -27), ([0, 0, 1, -1, 0, 1, -1], -27)]

def combined97_part1 : Sparse := [([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 1, -2], -27), ([1, -2, 1, 0, 0, 1, 0], -9), ([1, -2, 1, 1, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 0, 0, 2, -1], -27), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 0, 2, -1], 18), ([1, -1, 1, -1, 1, 1, -1], -18), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, -1, 2, -1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 1, 1, -2], 18), ([1, -1, 1, 1, -1, 1, -1], -18), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 0, 1, -2], 9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], 9)]

def combined97_part2 : Sparse := [([1, 0, 1, 0, 0, 1, -2], -27)]

def combined97 : Sparse := combined97_part0 ++ combined97_part1 ++ combined97_part2

def combined98_part0 : Sparse := [([0, -2, 1, 0, 0, 2, -1], -27), ([0, -2, 2, 0, 0, 1, -1], -27), ([0, -1, 0, 0, 0, 2, -1], -9), ([0, -1, 0, 0, 1, 1, -1], -27), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 1, -1, 0, 1, 0], -27), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 1, -1], -9), ([0, -1, 1, 0, -1, 1, 0], -27), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 0, 0, 2, -2], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, -1, 1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], -27), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, -1, 2, 0, 0, 0, -1], -9), ([0, -1, 2, 0, 0, 1, -2], -18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([0, 0, 1, 0, 0, 1, -2], -18), ([1, -2, 1, 0, 1, 1, -1], 9), ([1, -2, 1, 1, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 1, 0], 9)]

def combined98_part1 : Sparse := [([1, -1, 0, 0, 0, 2, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, -1, 0, 2, -1], 18), ([1, -1, 1, -1, 1, 1, -1], -9), ([1, -1, 1, 0, -1, 2, -1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 1, 1, -2], 18), ([1, -1, 1, 1, -1, 1, -1], -9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 0, 1, -2], 18), ([1, -1, 2, -1, 0, 1, -1], 9), ([1, -1, 2, 0, -1, 1, -1], 18), ([1, -1, 2, 0, 0, 0, -1], -9), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 1, 0, 0, 0, -1], 18), ([1, 0, 1, 0, 0, 1, -2], -18)]

def combined98 : Sparse := combined98_part0 ++ combined98_part1

def combined99 : Sparse := [([0, -2, 1, 0, 0, 2, -1], -18), ([0, -2, 2, 0, 0, 1, -1], -18), ([0, -1, 0, 0, 1, 1, -1], -18), ([0, -1, 0, 1, 0, 1, -1], -18), ([0, -1, 1, -1, 0, 1, 0], -18), ([0, -1, 1, 0, -1, 1, 0], -18), ([0, -1, 1, 0, 0, 2, -2], -18), ([0, -1, 1, 0, 1, 0, -1], -18), ([0, -1, 1, 1, 0, 0, -1], -18), ([0, -1, 2, 0, 0, 1, -2], -18), ([0, 0, 1, -1, 0, 1, -1], -18), ([0, 0, 1, 0, -1, 1, -1], -18), ([1, -2, 1, 0, 1, 1, -1], 18), ([1, -2, 1, 1, 0, 1, -1], 18), ([1, -1, 0, 0, 0, 1, 0], 18), ([1, -1, 1, -1, 0, 2, -1], 18), ([1, -1, 1, 0, -1, 2, -1], 18), ([1, -1, 1, 0, 0, 0, 0], 18), ([1, -1, 1, 0, 1, 1, -2], 18), ([1, -1, 1, 1, 0, 1, -2], 18), ([1, -1, 2, -1, 0, 1, -1], 18), ([1, -1, 2, 0, -1, 1, -1], 18), ([1, 0, 0, 0, 0, 1, -1], 18), ([1, 0, 1, 0, 0, 0, -1], 18)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined476_part8 : Sparse := [([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 1, 1, 0], -144), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 1, 0, 0, 1], 144), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36), ([1, -1, 0, -1, 0, 1, 1], -144), ([1, -1, 0, -1, 0, 2, 0], -36), ([1, -1, 0, -1, 2, 0, 0], 36), ([1, -1, 0, 0, -1, 0, 2], -36), ([1, -1, 0, 0, -1, 2, 0], 36), ([1, -1, 0, 0, 0, -1, 2], 36), ([1, -1, 0, 0, 0, 2, -1], 36), ([1, -1, 0, 0, 1, -1, 1], 144), ([1, -1, 0, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 2, 0, -1], -36), ([1, -1, 0, 1, -1, 1, 0], 144), ([1, -1, 0, 1, 1, 0, -1], -144), ([1, -1, 0, 2, -1, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], -36)]

def combined476_part9 : Sparse := [([1, -1, 0, 2, 0, 0, -1], -36), ([1, -1, 1, -1, 1, 0, 0], 144), ([1, -1, 1, 0, -1, 0, 1], -144), ([1, -1, 1, 0, 0, 1, -1], 144), ([1, -1, 1, 1, 0, -1, 0], -144), ([1, -1, 2, -1, 0, 0, 0], 36), ([1, -1, 2, 0, -1, 0, 0], -36), ([1, -1, 2, 0, 0, -1, 0], -36), ([1, -1, 2, 0, 0, 0, -1], 36), ([1, 0, -2, 0, 0, 1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], -36), ([1, 0, -2, 0, 1, 1, 0], -36), ([1, 0, -2, 1, 0, 0, 1], 36), ([1, 0, -2, 1, 0, 1, 0], -36), ([1, 0, -2, 1, 1, 0, 0], 36), ([1, 0, -1, -1, 0, 0, 2], -36), ([1, 0, -1, -1, 0, 2, 0], 36), ([1, 0, -1, -1, 1, 0, 1], -144), ([1, 0, -1, -1, 2, 0, 0], -36), ([1, 0, -1, 0, -1, 0, 2], 36), ([1, 0, -1, 0, -1, 1, 1], 144), ([1, 0, -1, 0, -1, 2, 0], 36), ([1, 0, -1, 0, 0, -1, 2], -36), ([1, 0, -1, 0, 0, 2, -1], -36)]

def combined477_part0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 0, 0, 1, 1], -144), ([0, -1, -1, 0, 1, 0, 1], -144), ([0, -1, -1, 1, 0, 0, 1], 144), ([0, -1, -1, 1, 0, 1, 0], -144), ([0, -1, -1, 1, 1, 0, 0], -144), ([0, -1, -1, 2, 0, 0, 0], 36), ([0, -1, 0, -1, 1, 0, 1], -144), ([0, -1, 0, -1, 1, 1, 0], -144), ([0, -1, 0, -1, 2, 0, 0], 36), ([0, -1, 0, 0, -1, 1, 1], -144), ([0, -1, 0, 0, -1, 2, 0], 36), ([0, -1, 0, 0, 0, -1, 2], 36), ([0, -1, 0, 0, 0, 2, -1], 36)]

def combined477_part1 : Sparse := [([0, -1, 0, 0, 1, -1, 1], 144), ([0, -1, 0, 0, 1, 1, -1], -144), ([0, -1, 0, 0, 2, -1, 0], 36), ([0, -1, 0, 1, -1, 0, 1], -144), ([0, -1, 0, 1, -1, 1, 0], 144), ([0, -1, 0, 1, 0, -1, 1], -144), ([0, -1, 0, 1, 0, 1, -1], -144), ([0, -1, 0, 1, 1, -1, 0], -144), ([0, -1, 0, 2, -1, 0, 0], 36), ([0, -1, 1, -1, 0, 0, 1], -144), ([0, -1, 1, -1, 0, 1, 0], -144), ([0, -1, 1, -1, 1, 0, 0], 144), ([0, -1, 1, 0, -1, 1, 0], -144), ([0, -1, 1, 0, 0, -1, 1], -144), ([0, -1, 1, 0, 0, 1, -1], 144), ([0, -1, 1, 0, 1, -1, 0], -144), ([0, -1, 1, 0, 1, 0, -1], -144), ([0, -1, 1, 1, -1, 0, 0], -144), ([0, -1, 1, 1, 0, 0, -1], -144), ([0, -1, 2, -1, 0, 0, 0], 36), ([0, -1, 2, 0, 0, 0, -1], 36), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -3, 0, 3, 0, 0], 36)]

def combined477_part2 : Sparse := [([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, -2, 0, 0, 1, 1], 36), ([0, 0, -2, 1, 0, 0, 1], 36), ([0, 0, -2, 1, 1, 0, 0], 36), ([0, 0, -1, -1, 0, 1, 1], -144), ([0, 0, -1, -1, 0, 2, 0], 36), ([0, 0, -1, -1, 1, 1, 0], -144), ([0, 0, -1, 0, -1, 0, 2], 36), ([0, 0, -1, 0, -1, 1, 1], 144), ([0, 0, -1, 0, -1, 2, 0], 36), ([0, 0, -1, 0, 1, -1, 1], -144), ([0, 0, -1, 0, 1, 1, -1], -144), ([0, 0, -1, 0, 2, -1, 0], 36), ([0, 0, -1, 0, 2, 0, -1], 36), ([0, 0, -1, 1, -1, 0, 1], -144), ([0, 0, -1, 1, -1, 1, 0], -144), ([0, 0, -1, 1, 0, -1, 1], -144), ([0, 0, -1, 1, 1, -1, 0], 144), ([0, 0, -1, 1, 1, 0, -1], -144), ([0, 0, -1, 2, 0, -1, 0], 36), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 36)]

def combined477_part3 : Sparse := [([0, 0, 0, -1, -1, 0, 2], 36), ([0, 0, 0, -1, -1, 1, 1], -144), ([0, 0, 0, -1, 0, -1, 2], 36), ([0, 0, 0, -1, 0, 2, -1], 36), ([0, 0, 0, -1, 1, -1, 1], -144), ([0, 0, 0, -1, 1, 0, 0], -18), ([0, 0, 0, -1, 1, 1, -1], 126), ([0, 0, 0, -1, 2, 0, -1], 36), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, -2, 1, 1], 36), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 1, -2, 1], 36), ([0, 0, 0, 0, 1, 0, -1], 18), ([0, 0, 0, 0, 1, 1, -2], 36), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 0, 1, -2, 1, 0], 36), ([0, 0, 0, 1, -1, 1, -1], -144), ([0, 0, 0, 1, 1, -2, 0], 36), ([0, 0, 0, 1, 1, -1, -1], -144), ([0, 0, 0, 2, -1, 0, -1], 36), ([0, 0, 0, 2, 0, -1, -1], 36)]

def combined477_part4 : Sparse := [([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 0, 3, 0, -3, 0], 36), ([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 1, -2, 0, 0, 1], 36), ([0, 0, 1, -2, 1, 0, 0], 36), ([0, 0, 1, -1, -1, 0, 1], -144), ([0, 0, 1, -1, 0, -1, 1], 144), ([0, 0, 1, -1, 0, 1, -1], -144), ([0, 0, 1, -1, 1, -1, 0], -144), ([0, 0, 1, -1, 1, 0, -1], -126), ([0, 0, 1, 0, -1, -1, 1], -144), ([0, 0, 1, 0, -1, 1, -1], -144), ([0, 0, 1, 0, 0, -2, 1], 36), ([0, 0, 1, 0, 0, 1, -2], 36), ([0, 0, 1, 1, -2, 0, 0], 36), ([0, 0, 1, 1, -1, -1, 0], -144), ([0, 0, 1, 1, -1, 0, -1], 144), ([0, 0, 1, 1, 0, -1, -1], -144), ([0, 0, 1, 1, 0, 0, -2], 36), ([0, 0, 2, -1, 0, -1, 0], 36), ([0, 0, 2, 0, -1, -1, 0], 36), ([0, 0, 2, 0, -1, 0, -1], 36), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 0, 3, 0, -3, 0, 0], 36)]

def combined477_part5 : Sparse := [([0, 0, 3, 0, 0, -3, 0], 36), ([0, 0, 3, 0, 0, 0, -3], 36), ([0, 1, -2, 0, 0, 1, 0], 36), ([0, 1, -2, 0, 1, 0, 0], 36), ([0, 1, -1, -1, 0, 0, 1], -144), ([0, 1, -1, -1, 0, 1, 0], 144), ([0, 1, -1, -1, 1, 0, 0], -126), ([0, 1, -1, -1, 2, 0, -1], 18), ([0, 1, -1, 0, -1, 0, 1], -144), ([0, 1, -1, 0, -1, 1, 0], -144), ([0, 1, -1, 0, 0, 1, -1], -144), ([0, 1, -1, 0, 1, -1, 0], -144), ([0, 1, -1, 0, 1, 0, -1], 126), ([0, 1, -1, 1, 0, -1, 0], -144), ([0, 1, -1, 1, 0, 0, -1], -144), ([0, 1, 0, -2, 0, 0, 1], 36), ([0, 1, 0, -2, 0, 1, 0], 36), ([0, 1, 0, -2, 1, 1, -1], -18), ([0, 1, 0, -2, 2, 0, -1], 18), ([0, 1, 0, -1, -1, 0, 1], 144), ([0, 1, 0, -1, -1, 1, 0], -144), ([0, 1, 0, -1, 0, -1, 1], -144), ([0, 1, 0, -1, 0, 1, -1], -126), ([0, 1, 0, -1, 1, 0, -1], -144)]

def combined477_part6 : Sparse := [([0, 1, 0, -1, 1, 1, -2], 18), ([0, 1, 0, -1, 2, -1, -1], -18), ([0, 1, 0, -1, 2, 0, -2], -18), ([0, 1, 0, 0, -2, 0, 1], 36), ([0, 1, 0, 0, -1, -1, 1], -144), ([0, 1, 0, 0, 0, 0, -1], -18), ([0, 1, 0, 0, 1, -1, -1], -126), ([0, 1, 0, 0, 1, 0, -2], 36), ([0, 1, 0, 1, -1, -1, 0], -144), ([0, 1, 0, 1, -1, 0, -1], -144), ([0, 1, 0, 1, 0, -2, 0], 36), ([0, 1, 0, 1, 0, -1, -1], 144), ([0, 1, 0, 1, 0, 0, -2], 36), ([0, 1, 1, -1, -1, 0, 0], -144), ([0, 1, 1, -1, 0, -1, 0], -144), ([0, 1, 1, -1, 1, 0, -2], -18), ([0, 1, 1, 0, -2, 0, 0], 36), ([0, 1, 1, 0, -1, -1, 0], 144), ([0, 1, 1, 0, -1, 0, -1], -144), ([0, 1, 1, 0, 0, -2, 0], 36), ([0, 1, 1, 0, 0, -1, -1], -144), ([0, 2, -1, -1, 0, 0, 0], 36), ([0, 2, -1, -1, 1, 0, -1], -18), ([0, 2, -1, 0, 0, 0, -1], 36)]

def combined477_part7 : Sparse := [([0, 2, 0, -1, -1, 0, 0], 36), ([0, 2, 0, -1, 1, 0, -2], 18), ([0, 2, 0, 0, -1, -1, 0], 36), ([0, 2, 0, 0, 0, -1, -1], 36), ([0, 3, -3, 0, 0, 0, 0], 36), ([0, 3, 0, -3, 0, 0, 0], 36), ([0, 3, 0, 0, -3, 0, 0], 36), ([0, 3, 0, 0, 0, -3, 0], 36), ([0, 3, 0, 0, 0, 0, -3], 36), ([1, -2, 0, 0, 0, 1, 1], -36), ([1, -2, 0, 0, 1, 0, 1], 36), ([1, -2, 0, 0, 1, 1, 0], -36), ([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 1, 1, 0], -144), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 1, 0, 0, 1], 144)]

def combined477_part8 : Sparse := [([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36), ([1, -1, 0, -1, 0, 1, 1], -144), ([1, -1, 0, -1, 0, 2, 0], -36), ([1, -1, 0, -1, 2, 0, 0], 36), ([1, -1, 0, 0, -1, 0, 2], -36), ([1, -1, 0, 0, -1, 2, 0], 36), ([1, -1, 0, 0, 0, -1, 2], 36), ([1, -1, 0, 0, 0, 2, -1], 36), ([1, -1, 0, 0, 1, -1, 1], 144), ([1, -1, 0, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 2, 0, -1], -36), ([1, -1, 0, 1, -1, 1, 0], 144), ([1, -1, 0, 1, 1, 0, -1], -144), ([1, -1, 0, 2, -1, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], -36), ([1, -1, 0, 2, 0, 0, -1], -36), ([1, -1, 1, -1, 1, 0, 0], 144), ([1, -1, 1, 0, -1, 0, 1], -144), ([1, -1, 1, 0, 0, 1, -1], 144), ([1, -1, 1, 1, 0, -1, 0], -144), ([1, -1, 2, -1, 0, 0, 0], 36), ([1, -1, 2, 0, -1, 0, 0], -36), ([1, -1, 2, 0, 0, -1, 0], -36)]

def combined477_part9 : Sparse := [([1, -1, 2, 0, 0, 0, -1], 36), ([1, 0, -2, 0, 0, 1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], -36), ([1, 0, -2, 0, 1, 1, 0], -36), ([1, 0, -2, 1, 0, 0, 1], 36), ([1, 0, -2, 1, 0, 1, 0], -36), ([1, 0, -2, 1, 1, 0, 0], 36), ([1, 0, -1, -1, 0, 0, 2], -36), ([1, 0, -1, -1, 0, 2, 0], 36), ([1, 0, -1, -1, 1, 0, 1], -144), ([1, 0, -1, -1, 2, 0, 0], -36), ([1, 0, -1, 0, -1, 0, 2], 36), ([1, 0, -1, 0, -1, 1, 1], 144), ([1, 0, -1, 0, -1, 2, 0], 36), ([1, 0, -1, 0, 0, -1, 2], -36), ([1, 0, -1, 0, 0, 2, -1], -36), ([1, 0, -1, 0, 2, -1, 0], 36), ([1, 0, -1, 0, 2, 0, -1], 36), ([1, 0, -1, 1, 0, 1, -1], -144), ([1, 0, -1, 1, 1, -1, 0], 144), ([1, 0, -1, 2, -1, 0, 0], -36), ([1, 0, -1, 2, 0, -1, 0], 36), ([1, 0, -1, 2, 0, 0, -1], -36), ([1, 0, 0, -2, 0, 1, 1], -36)]

def combined477_part10 : Sparse := [([1, 0, 0, -2, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 1, 0], 36), ([1, 0, 0, -1, -1, 0, 2], 36), ([1, 0, 0, -1, -1, 2, 0], -36), ([1, 0, 0, -1, 0, -1, 2], 36), ([1, 0, 0, -1, 0, 2, -1], 36), ([1, 0, 0, -1, 1, 1, -1], 126), ([1, 0, 0, -1, 2, -1, 0], -36), ([1, 0, 0, -1, 2, 0, -1], 36), ([1, 0, 0, 0, -2, 1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], -36), ([1, 0, 0, 0, -1, 2, -1], -36), ([1, 0, 0, 0, 1, -2, 1], 36), ([1, 0, 0, 0, 1, 0, -1], 18), ([1, 0, 0, 0, 1, 1, -2], 36), ([1, 0, 0, 0, 2, -1, -1], -36), ([1, 0, 0, 1, -2, 0, 1], -36), ([1, 0, 0, 1, -2, 1, 0], 36), ([1, 0, 0, 1, -1, -1, 1], -144), ([1, 0, 0, 1, 0, -2, 1], -36), ([1, 0, 0, 1, 0, 1, -2], -36), ([1, 0, 0, 1, 1, -2, 0], 36), ([1, 0, 0, 1, 1, 0, -2], -36), ([1, 0, 0, 2, -1, -1, 0], -36)]

def combined477_part11 : Sparse := [([1, 0, 0, 2, -1, 0, -1], 36), ([1, 0, 0, 2, 0, -1, -1], 36), ([1, 0, 1, -2, 0, 0, 1], 36), ([1, 0, 1, -2, 0, 1, 0], -36), ([1, 0, 1, -2, 1, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -144), ([1, 0, 1, -1, 0, -1, 1], 144), ([1, 0, 1, 0, -2, 0, 1], -36), ([1, 0, 1, 0, -2, 1, 0], -36), ([1, 0, 1, 0, 0, -2, 1], 36), ([1, 0, 1, 0, 0, 1, -2], 36), ([1, 0, 1, 0, 1, -2, 0], -36), ([1, 0, 1, 0, 1, -1, -1], -144), ([1, 0, 1, 0, 1, 0, -2], -36), ([1, 0, 1, 1, -2, 0, 0], 36), ([1, 0, 1, 1, -1, 0, -1], 144), ([1, 0, 1, 1, 0, -2, 0], -36), ([1, 0, 1, 1, 0, 0, -2], 36), ([1, 0, 2, -1, -1, 0, 0], -36), ([1, 0, 2, -1, 0, -1, 0], 36), ([1, 0, 2, -1, 0, 0, -1], -36), ([1, 0, 2, 0, -1, -1, 0], 36), ([1, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 2, 0, 0, -1, -1], -36)]

def combined477_part12 : Sparse := [([1, 1, -2, 0, 0, 0, 1], -36), ([1, 1, -2, 0, 0, 1, 0], 36), ([1, 1, -2, 0, 1, 0, 0], 36), ([1, 1, -2, 1, 0, 0, 0], -36), ([1, 1, -1, -1, 0, 1, 0], 144), ([1, 1, -1, -1, 2, 0, -1], 18), ([1, 1, -1, 0, 0, -1, 1], -144), ([1, 1, -1, 0, 1, 0, -1], 126), ([1, 1, -1, 1, -1, 0, 0], -144), ([1, 1, 0, -2, 0, 0, 1], 36), ([1, 1, 0, -2, 0, 1, 0], 36), ([1, 1, 0, -2, 1, 0, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 144), ([1, 1, 0, -1, 0, 0, 0], -18), ([1, 1, 0, -1, 1, -1, 0], -126), ([1, 1, 0, -1, 1, 1, -2], 18), ([1, 1, 0, -1, 2, 0, -2], -18), ([1, 1, 0, 0, -2, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], -36), ([1, 1, 0, 0, -1, 1, -1], -144), ([1, 1, 0, 0, 0, -2, 1], -36), ([1, 1, 0, 0, 0, 1, -2], -36), ([1, 1, 0, 0, 1, -2, 0], -36), ([1, 1, 0, 0, 1, 0, -2], 36)]

def combined477_part13 : Sparse := [([1, 1, 0, 1, -2, 0, 0], -36), ([1, 1, 0, 1, 0, -2, 0], 36), ([1, 1, 0, 1, 0, -1, -1], 144), ([1, 1, 0, 1, 0, 0, -2], 36), ([1, 1, 1, -2, 0, 0, 0], -36), ([1, 1, 1, -2, 1, 0, -1], -18), ([1, 1, 1, -1, 0, 0, -1], -126), ([1, 1, 1, 0, -2, 0, 0], 36), ([1, 1, 1, 0, -1, -1, 0], 144), ([1, 1, 1, 0, 0, -2, 0], 36), ([1, 1, 1, 0, 0, 0, -2], -36), ([1, 2, -1, -1, 0, 0, 0], 36), ([1, 2, -1, 0, -1, 0, 0], -36), ([1, 2, -1, 0, 0, -1, 0], -36), ([1, 2, -1, 0, 0, 0, -1], 36), ([1, 2, 0, -2, 1, 0, -1], 18), ([1, 2, 0, -1, -1, 0, 0], 36), ([1, 2, 0, -1, 0, -1, 0], -36), ([1, 2, 0, -1, 0, 0, -1], -36), ([1, 2, 0, -1, 1, -1, -1], -18), ([1, 2, 0, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -1, 0, -1], -36), ([1, 2, 0, 0, 0, -1, -1], 36)]

def combined477 : Sparse := combined477_part0 ++ combined477_part1 ++ combined477_part2 ++ combined477_part3 ++ combined477_part4 ++ combined477_part5 ++ combined477_part6 ++ combined477_part7 ++ combined477_part8 ++ combined477_part9 ++ combined477_part10 ++ combined477_part11 ++ combined477_part12 ++ combined477_part13

def combined478_part0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 0, 0, 1, 1], -144), ([0, -1, -1, 0, 1, 0, 1], -144), ([0, -1, -1, 1, 0, 0, 1], 144), ([0, -1, -1, 1, 0, 1, 0], -144), ([0, -1, -1, 1, 1, 0, 0], -144), ([0, -1, -1, 2, 0, 0, 0], 36), ([0, -1, 0, -1, 1, 0, 1], -144), ([0, -1, 0, -1, 1, 1, 0], -144), ([0, -1, 0, -1, 2, 0, 0], 36), ([0, -1, 0, 0, -1, 1, 1], -144), ([0, -1, 0, 0, -1, 2, 0], 36), ([0, -1, 0, 0, 0, -1, 2], 36), ([0, -1, 0, 0, 0, 2, -1], 36)]

def combined478_part1 : Sparse := [([0, -1, 0, 0, 1, -1, 1], 144), ([0, -1, 0, 0, 1, 1, -1], -144), ([0, -1, 0, 0, 2, -1, 0], 36), ([0, -1, 0, 1, -1, 0, 1], -144), ([0, -1, 0, 1, -1, 1, 0], 144), ([0, -1, 0, 1, 0, -1, 1], -144), ([0, -1, 0, 1, 0, 1, -1], -144), ([0, -1, 0, 1, 1, -1, 0], -144), ([0, -1, 0, 2, -1, 0, 0], 36), ([0, -1, 1, -1, 0, 0, 1], -144), ([0, -1, 1, -1, 0, 1, 0], -144), ([0, -1, 1, -1, 1, 0, 0], 144), ([0, -1, 1, 0, -1, 1, 0], -144), ([0, -1, 1, 0, 0, -1, 1], -144), ([0, -1, 1, 0, 0, 1, -1], 144), ([0, -1, 1, 0, 1, -1, 0], -144), ([0, -1, 1, 0, 1, 0, -1], -144), ([0, -1, 1, 1, -1, 0, 0], -144), ([0, -1, 1, 1, 0, 0, -1], -144), ([0, -1, 2, -1, 0, 0, 0], 36), ([0, -1, 2, 0, 0, 0, -1], 36), ([0, 0, -3, 0, 0, 0, 3], 36), ([0, 0, -3, 0, 0, 3, 0], 36), ([0, 0, -3, 0, 3, 0, 0], 36)]

def combined478_part2 : Sparse := [([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, -2, 0, 0, 1, 1], 36), ([0, 0, -2, 1, 0, 0, 1], 36), ([0, 0, -2, 1, 1, 0, 0], 36), ([0, 0, -1, -1, 0, 1, 1], -144), ([0, 0, -1, -1, 0, 2, 0], 36), ([0, 0, -1, -1, 1, 1, 0], -144), ([0, 0, -1, 0, -1, 0, 2], 36), ([0, 0, -1, 0, -1, 1, 1], 144), ([0, 0, -1, 0, -1, 2, 0], 36), ([0, 0, -1, 0, 1, -1, 1], -144), ([0, 0, -1, 0, 1, 1, -1], -144), ([0, 0, -1, 0, 2, -1, 0], 36), ([0, 0, -1, 0, 2, 0, -1], 36), ([0, 0, -1, 1, -1, 0, 1], -144), ([0, 0, -1, 1, -1, 1, 0], -144), ([0, 0, -1, 1, 0, -1, 1], -144), ([0, 0, -1, 1, 1, -1, 0], 144), ([0, 0, -1, 1, 1, 0, -1], -144), ([0, 0, -1, 2, 0, -1, 0], 36), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 36)]

def combined478_part3 : Sparse := [([0, 0, 0, -1, -1, 0, 2], 36), ([0, 0, 0, -1, -1, 1, 1], -144), ([0, 0, 0, -1, 0, -1, 2], 36), ([0, 0, 0, -1, 0, 2, -1], 36), ([0, 0, 0, -1, 1, -1, 1], -144), ([0, 0, 0, -1, 1, 1, -1], 144), ([0, 0, 0, -1, 2, 0, -1], 36), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, -2, 1, 1], 36), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 1, -2, 1], 36), ([0, 0, 0, 0, 1, 1, -2], 36), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 0, 1, -2, 1, 0], 36), ([0, 0, 0, 1, -1, 1, -1], -144), ([0, 0, 0, 1, 1, -2, 0], 36), ([0, 0, 0, 1, 1, -1, -1], -144), ([0, 0, 0, 2, -1, 0, -1], 36), ([0, 0, 0, 2, 0, -1, -1], 36), ([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 0, 3, 0, -3, 0], 36)]

def combined478_part4 : Sparse := [([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 1, -2, 0, 0, 1], 36), ([0, 0, 1, -2, 1, 0, 0], 36), ([0, 0, 1, -1, -1, 0, 1], -144), ([0, 0, 1, -1, 0, -1, 1], 144), ([0, 0, 1, -1, 0, 1, -1], -144), ([0, 0, 1, -1, 1, -1, 0], -144), ([0, 0, 1, -1, 1, 0, -1], -144), ([0, 0, 1, 0, -1, -1, 1], -144), ([0, 0, 1, 0, -1, 1, -1], -144), ([0, 0, 1, 0, 0, -2, 1], 36), ([0, 0, 1, 0, 0, 1, -2], 36), ([0, 0, 1, 1, -2, 0, 0], 36), ([0, 0, 1, 1, -1, -1, 0], -144), ([0, 0, 1, 1, -1, 0, -1], 144), ([0, 0, 1, 1, 0, -1, -1], -144), ([0, 0, 1, 1, 0, 0, -2], 36), ([0, 0, 2, -1, 0, -1, 0], 36), ([0, 0, 2, 0, -1, -1, 0], 36), ([0, 0, 2, 0, -1, 0, -1], 36), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 0, 3, 0, -3, 0, 0], 36), ([0, 0, 3, 0, 0, -3, 0], 36), ([0, 0, 3, 0, 0, 0, -3], 36)]

def combined478_part5 : Sparse := [([0, 1, -2, 0, 0, 1, 0], 36), ([0, 1, -2, 0, 1, 0, 0], 36), ([0, 1, -1, -1, 0, 0, 1], -144), ([0, 1, -1, -1, 0, 1, 0], 144), ([0, 1, -1, -1, 1, 0, 0], -144), ([0, 1, -1, 0, -1, 0, 1], -144), ([0, 1, -1, 0, -1, 1, 0], -144), ([0, 1, -1, 0, 0, 1, -1], -144), ([0, 1, -1, 0, 1, -1, 0], -144), ([0, 1, -1, 0, 1, 0, -1], 144), ([0, 1, -1, 1, 0, -1, 0], -144), ([0, 1, -1, 1, 0, 0, -1], -144), ([0, 1, 0, -2, 0, 0, 1], 36), ([0, 1, 0, -2, 0, 1, 0], 36), ([0, 1, 0, -1, -1, 0, 1], 144), ([0, 1, 0, -1, -1, 1, 0], -144), ([0, 1, 0, -1, 0, -1, 1], -144), ([0, 1, 0, -1, 0, 1, -1], -144), ([0, 1, 0, -1, 1, 0, -1], -144), ([0, 1, 0, 0, -2, 0, 1], 36), ([0, 1, 0, 0, -1, -1, 1], -144), ([0, 1, 0, 0, 1, -1, -1], -144), ([0, 1, 0, 0, 1, 0, -2], 36), ([0, 1, 0, 1, -1, -1, 0], -144)]

def combined478_part6 : Sparse := [([0, 1, 0, 1, -1, 0, -1], -144), ([0, 1, 0, 1, 0, -2, 0], 36), ([0, 1, 0, 1, 0, -1, -1], 144), ([0, 1, 0, 1, 0, 0, -2], 36), ([0, 1, 1, -1, -1, 0, 0], -144), ([0, 1, 1, -1, 0, -1, 0], -144), ([0, 1, 1, 0, -2, 0, 0], 36), ([0, 1, 1, 0, -1, -1, 0], 144), ([0, 1, 1, 0, -1, 0, -1], -144), ([0, 1, 1, 0, 0, -2, 0], 36), ([0, 1, 1, 0, 0, -1, -1], -144), ([0, 2, -1, -1, 0, 0, 0], 36), ([0, 2, -1, 0, 0, 0, -1], 36), ([0, 2, 0, -1, -1, 0, 0], 36), ([0, 2, 0, 0, -1, -1, 0], 36), ([0, 2, 0, 0, 0, -1, -1], 36), ([0, 3, -3, 0, 0, 0, 0], 36), ([0, 3, 0, -3, 0, 0, 0], 36), ([0, 3, 0, 0, -3, 0, 0], 36), ([0, 3, 0, 0, 0, -3, 0], 36), ([0, 3, 0, 0, 0, 0, -3], 36), ([1, -2, 0, 0, 0, 1, 1], -36), ([1, -2, 0, 0, 1, 0, 1], 36), ([1, -2, 0, 0, 1, 1, 0], -36)]

def combined478_part7 : Sparse := [([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 1, 1, 0], -144), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 1, 0, 0, 1], 144), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36), ([1, -1, 0, -1, 0, 1, 1], -144), ([1, -1, 0, -1, 0, 2, 0], -36), ([1, -1, 0, -1, 2, 0, 0], 36), ([1, -1, 0, 0, -1, 0, 2], -36), ([1, -1, 0, 0, -1, 2, 0], 36), ([1, -1, 0, 0, 0, -1, 2], 36), ([1, -1, 0, 0, 0, 2, -1], 36), ([1, -1, 0, 0, 1, -1, 1], 144), ([1, -1, 0, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 2, 0, -1], -36)]

def combined478_part8 : Sparse := [([1, -1, 0, 1, -1, 1, 0], 144), ([1, -1, 0, 1, 1, 0, -1], -144), ([1, -1, 0, 2, -1, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], -36), ([1, -1, 0, 2, 0, 0, -1], -36), ([1, -1, 1, -1, 1, 0, 0], 144), ([1, -1, 1, 0, -1, 0, 1], -144), ([1, -1, 1, 0, 0, 1, -1], 144), ([1, -1, 1, 1, 0, -1, 0], -144), ([1, -1, 2, -1, 0, 0, 0], 36), ([1, -1, 2, 0, -1, 0, 0], -36), ([1, -1, 2, 0, 0, -1, 0], -36), ([1, -1, 2, 0, 0, 0, -1], 36), ([1, 0, -2, 0, 0, 1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], -36), ([1, 0, -2, 0, 1, 1, 0], -36), ([1, 0, -2, 1, 0, 0, 1], 36), ([1, 0, -2, 1, 0, 1, 0], -36), ([1, 0, -2, 1, 1, 0, 0], 36), ([1, 0, -1, -1, 0, 0, 2], -36), ([1, 0, -1, -1, 0, 2, 0], 36), ([1, 0, -1, -1, 1, 0, 1], -144), ([1, 0, -1, -1, 2, 0, 0], -36), ([1, 0, -1, 0, -1, 0, 2], 36)]

def combined478_part9 : Sparse := [([1, 0, -1, 0, -1, 1, 1], 144), ([1, 0, -1, 0, -1, 2, 0], 36), ([1, 0, -1, 0, 0, -1, 2], -36), ([1, 0, -1, 0, 0, 2, -1], -36), ([1, 0, -1, 0, 2, -1, 0], 36), ([1, 0, -1, 0, 2, 0, -1], 36), ([1, 0, -1, 1, 0, 1, -1], -144), ([1, 0, -1, 1, 1, -1, 0], 144), ([1, 0, -1, 2, -1, 0, 0], -36), ([1, 0, -1, 2, 0, -1, 0], 36), ([1, 0, -1, 2, 0, 0, -1], -36), ([1, 0, 0, -2, 0, 1, 1], -36), ([1, 0, 0, -2, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 1, 0], 36), ([1, 0, 0, -1, -1, 0, 2], 36), ([1, 0, 0, -1, -1, 2, 0], -36), ([1, 0, 0, -1, 0, -1, 2], 36), ([1, 0, 0, -1, 0, 2, -1], 36), ([1, 0, 0, -1, 1, 1, -1], 144), ([1, 0, 0, -1, 2, -1, 0], -36), ([1, 0, 0, -1, 2, 0, -1], 36), ([1, 0, 0, 0, -2, 1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], -36), ([1, 0, 0, 0, -1, 2, -1], -36)]

def combined478_part10 : Sparse := [([1, 0, 0, 0, 1, -2, 1], 36), ([1, 0, 0, 0, 1, 1, -2], 36), ([1, 0, 0, 0, 2, -1, -1], -36), ([1, 0, 0, 1, -2, 0, 1], -36), ([1, 0, 0, 1, -2, 1, 0], 36), ([1, 0, 0, 1, -1, -1, 1], -144), ([1, 0, 0, 1, 0, -2, 1], -36), ([1, 0, 0, 1, 0, 1, -2], -36), ([1, 0, 0, 1, 1, -2, 0], 36), ([1, 0, 0, 1, 1, 0, -2], -36), ([1, 0, 0, 2, -1, -1, 0], -36), ([1, 0, 0, 2, -1, 0, -1], 36), ([1, 0, 0, 2, 0, -1, -1], 36), ([1, 0, 1, -2, 0, 0, 1], 36), ([1, 0, 1, -2, 0, 1, 0], -36), ([1, 0, 1, -2, 1, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -144), ([1, 0, 1, -1, 0, -1, 1], 144), ([1, 0, 1, 0, -2, 0, 1], -36), ([1, 0, 1, 0, -2, 1, 0], -36), ([1, 0, 1, 0, 0, -2, 1], 36), ([1, 0, 1, 0, 0, 1, -2], 36), ([1, 0, 1, 0, 1, -2, 0], -36), ([1, 0, 1, 0, 1, -1, -1], -144)]

def combined478_part11 : Sparse := [([1, 0, 1, 0, 1, 0, -2], -36), ([1, 0, 1, 1, -2, 0, 0], 36), ([1, 0, 1, 1, -1, 0, -1], 144), ([1, 0, 1, 1, 0, -2, 0], -36), ([1, 0, 1, 1, 0, 0, -2], 36), ([1, 0, 2, -1, -1, 0, 0], -36), ([1, 0, 2, -1, 0, -1, 0], 36), ([1, 0, 2, -1, 0, 0, -1], -36), ([1, 0, 2, 0, -1, -1, 0], 36), ([1, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 2, 0, 0, -1, -1], -36), ([1, 1, -2, 0, 0, 0, 1], -36), ([1, 1, -2, 0, 0, 1, 0], 36), ([1, 1, -2, 0, 1, 0, 0], 36), ([1, 1, -2, 1, 0, 0, 0], -36), ([1, 1, -1, -1, 0, 1, 0], 144), ([1, 1, -1, 0, 0, -1, 1], -144), ([1, 1, -1, 0, 1, 0, -1], 144), ([1, 1, -1, 1, -1, 0, 0], -144), ([1, 1, 0, -2, 0, 0, 1], 36), ([1, 1, 0, -2, 0, 1, 0], 36), ([1, 1, 0, -2, 1, 0, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 144), ([1, 1, 0, -1, 1, -1, 0], -144)]

def combined478_part12 : Sparse := [([1, 1, 0, 0, -2, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], -36), ([1, 1, 0, 0, -1, 1, -1], -144), ([1, 1, 0, 0, 0, -2, 1], -36), ([1, 1, 0, 0, 0, 1, -2], -36), ([1, 1, 0, 0, 1, -2, 0], -36), ([1, 1, 0, 0, 1, 0, -2], 36), ([1, 1, 0, 1, -2, 0, 0], -36), ([1, 1, 0, 1, 0, -2, 0], 36), ([1, 1, 0, 1, 0, -1, -1], 144), ([1, 1, 0, 1, 0, 0, -2], 36), ([1, 1, 1, -2, 0, 0, 0], -36), ([1, 1, 1, -1, 0, 0, -1], -144), ([1, 1, 1, 0, -2, 0, 0], 36), ([1, 1, 1, 0, -1, -1, 0], 144), ([1, 1, 1, 0, 0, -2, 0], 36), ([1, 1, 1, 0, 0, 0, -2], -36), ([1, 2, -1, -1, 0, 0, 0], 36), ([1, 2, -1, 0, -1, 0, 0], -36), ([1, 2, -1, 0, 0, -1, 0], -36), ([1, 2, -1, 0, 0, 0, -1], 36), ([1, 2, 0, -1, -1, 0, 0], 36), ([1, 2, 0, -1, 0, -1, 0], -36), ([1, 2, 0, -1, 0, 0, -1], -36)]

def combined478_part13 : Sparse := [([1, 2, 0, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -1, 0, -1], -36), ([1, 2, 0, 0, 0, -1, -1], 36)]

def combined478 : Sparse := combined478_part0 ++ combined478_part1 ++ combined478_part2 ++ combined478_part3 ++ combined478_part4 ++ combined478_part5 ++ combined478_part6 ++ combined478_part7 ++ combined478_part8 ++ combined478_part9 ++ combined478_part10 ++ combined478_part11 ++ combined478_part12 ++ combined478_part13

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined1_part2 : Sparse := [([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36), ([1, -1, 0, -1, 0, 2, 0], -36), ([1, -1, 0, -1, 2, 0, 0], 36), ([1, -1, 0, 0, -1, 0, 2], -36), ([1, -1, 0, 0, -1, 2, 0], 36), ([1, -1, 0, 0, 0, -1, 2], 36), ([1, -1, 0, 0, 0, 2, -1], 36), ([1, -1, 0, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 2, 0, -1], -36), ([1, -1, 0, 2, -1, 0, 0], 36), ([1, -1, 0, 2, 0, -1, 0], -36), ([1, -1, 0, 2, 0, 0, -1], -36), ([1, -1, 2, -1, 0, 0, 0], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined10_part0 : Sparse := [([0, -3, 0, 0, 0, 0, 3], 36), ([0, -3, 0, 0, 0, 3, 0], 36), ([0, -3, 0, 0, 3, 0, 0], 36), ([0, -3, 0, 3, 0, 0, 0], 36), ([0, -3, 3, 0, 0, 0, 0], 36), ([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 0, 0, 1, 1], -144), ([0, -1, -1, 0, 1, 0, 1], -144), ([0, -1, -1, 1, 0, 0, 1], 144), ([0, -1, -1, 1, 0, 1, 0], -144), ([0, -1, -1, 1, 1, 0, 0], -144), ([0, -1, -1, 2, 0, 0, 0], 36), ([0, -1, 0, -1, 1, 0, 1], -144), ([0, -1, 0, -1, 1, 1, 0], -144), ([0, -1, 0, -1, 2, 0, 0], 36), ([0, -1, 0, 0, -1, 1, 1], -144), ([0, -1, 0, 0, -1, 2, 0], 36), ([0, -1, 0, 0, 0, -1, 2], 36), ([0, -1, 0, 0, 0, 2, -1], 36)]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def averageOtherFourier (U : Coord → CMatrix) (s : Coord) (a : Charge) : ℂ :=
  (5 : ℂ)⁻¹ * ∑ t : Fin 5, g (U (s.succAbove t)) a

end MUB6

end

end OAI
end


