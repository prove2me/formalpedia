-- Prove2me | Definitions.Def_OAIQ106E156
-- name    : OAIQ106E156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T02:52:08.513192+00:00
-- url     : https://prove2.me/theorems/8e733064-1b76-46e8-838b-e6d0655a364f
-- title:
--   Definitions bundle OAIQ106E156 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 18 definitions. The definitions and types are `OAI.MUB6.TaoArithmetic.cubeTerms`, `OAI.MUB6.TaoArithmetic.knownTerms`, `OAI.MUB6.TaoArithmetic.monomial`, `OAI.MUB6.TaoArithmetic.row`, `OAI.MUB6.TaoCertificate.knownParams0`, `OAI.MUB6.TaoCertificate.knownParams1`, `OAI.MUB6.TaoCertificate.knownParams10`, `OAI.MUB6.TaoCertificate.knownParams11`, `OAI.MUB6.TaoCertificate.knownParams12`, `OAI.MUB6.TaoCertificate.knownParams13`, `OAI.MUB6.TaoCertificate.knownParams2`, `OAI.MUB6.TaoCertificate.knownParams3`, `OAI.MUB6.TaoCertificate.knownParams4`, `OAI.MUB6.TaoCertificate.knownParams5`, `OAI.MUB6.TaoCertificate.knownParams6`, `OAI.MUB6.TaoCertificate.knownParams7`, `OAI.MUB6.TaoCertificate.knownParams8`, `OAI.MUB6.TaoCertificate.knownParams9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_TaoCertificate_KnownTarget0`, `MutuallyUnbiased_TaoCertificate_KnownTarget1`, `MutuallyUnbiased_TaoCertificate_KnownTarget10`, `MutuallyUnbiased_TaoCertificate_KnownTarget11`, `MutuallyUnbiased_TaoCertificate_KnownTarget12`, `MutuallyUnbiased_TaoCertificate_KnownTarget13`, `MutuallyUnbiased_TaoCertificate_KnownTarget2`, `MutuallyUnbiased_TaoCertificate_KnownTarget3`, `MutuallyUnbiased_TaoCertificate_KnownTarget4`, `MutuallyUnbiased_TaoCertificate_KnownTarget5`, `MutuallyUnbiased_TaoCertificate_KnownTarget6`, `MutuallyUnbiased_TaoCertificate_KnownTarget7`, `MutuallyUnbiased_TaoCertificate_KnownTarget8`, `MutuallyUnbiased_TaoCertificate_KnownTarget9`, `MutuallyUnbiased_Tao_TaoSparse`, `MutuallyUnbiased_Tao_TaoTarget`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E140` and `OAIQ106E155` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.TaoCertificate.combined377_zero_e`, `OAI.MUB6.TaoCertificate.combined396_zero_e`, `OAI.MUB6.TaoCertificate.combined414_zero_e`, `OAI.MUB6.TaoCertificate.combined438_zero_e`, `OAI.MUB6.TaoCertificate.combined455_zero_e`, `OAI.MUB6.TaoCertificate.combined474_zero_e` and `OAI.MUB6.complete_family_square_not_hadamard_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E155

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

def monomial (a : Charge) (z : Coeff) : Sparse :=
  [(0 :: encode a, z.1), (1 :: encode a, z.2)]

def row (a c : Charge) (w : Coeff) : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial (a + difference p.1 p.2)
    (mul w (conjugate (counts (c + difference p.1 p.2)))))

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def knownTerms (ps : List (Charge × Coeff)) : Sparse :=
  ps.flatMap (fun p => monomial p.1 p.2)

def cubeTerms : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial ((3 : ℤ) • difference p.1 p.2) (36, 0))

end MUB6.TaoArithmetic

end

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

end MUB6.TaoCertificate

end OAI
end


