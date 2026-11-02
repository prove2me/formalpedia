-- Prove2me | Definitions.Def_OAIQ106D085
-- name    : OAIQ106D085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:52:05.029472+00:00
-- url     : https://prove2.me/theorems/15abdb70-4a62-47b1-abe2-23e9df2201c9
-- title:
--   Definitions bundle OAIQ106D085 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 929 declarations of OpenAI's Lean: 929 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key1241`, `OAI.MUB6.Certificate.GramRows.key1242`, `OAI.MUB6.Certificate.GramRows.key1251`, `OAI.MUB6.Certificate.GramRows.key1252`, `OAI.MUB6.Certificate.GramRows.key1255`, `OAI.MUB6.Certificate.GramRows.key1258`, `OAI.MUB6.Certificate.GramRows.key1260`, `OAI.MUB6.Certificate.GramRows.key1264`, `OAI.MUB6.Certificate.GramRows.key1267`, `OAI.MUB6.Certificate.GramRows.key1270`, `OAI.MUB6.Certificate.GramRows.key1315`, `OAI.MUB6.Certificate.GramRows.key1318`, `OAI.MUB6.Certificate.GramRows.key1350`, `OAI.MUB6.Certificate.GramRows.key1423`, `OAI.MUB6.Certificate.GramRows.key1426`, `OAI.MUB6.Certificate.GramRows.key1764`, `OAI.MUB6.Certificate.GramRows.key1805`, `OAI.MUB6.Certificate.GramRows.key1808`, `OAI.MUB6.Certificate.GramRows.key1829`, `OAI.MUB6.Certificate.GramRows.key1893`, `OAI.MUB6.Certificate.GramRows.key1895`, `OAI.MUB6.Certificate.GramRows.key1915`, `OAI.MUB6.Certificate.GramRows.key1918`, `OAI.MUB6.Certificate.GramRows.key1929`, `OAI.MUB6.Certificate.GramRows.key2077`, `OAI.MUB6.Certificate.GramRows.key22`, `OAI.MUB6.Certificate.GramRows.key235`, `OAI.MUB6.Certificate.GramRows.key247`, `OAI.MUB6.Certificate.GramRows.key256`, `OAI.MUB6.Certificate.GramRows.key2584`, `OAI.MUB6.Certificate.GramRows.key2635`, `OAI.MUB6.Certificate.GramRows.key2721`, `OAI.MUB6.Certificate.GramRows.key2845`, `OAI.MUB6.Certificate.GramRows.key2988`, `OAI.MUB6.Certificate.GramRows.key301`, `OAI.MUB6.Certificate.GramRows.key315`, `OAI.MUB6.Certificate.GramRows.key326`, `OAI.MUB6.Certificate.GramRows.key34`, `OAI.MUB6.Certificate.GramRows.key746`, `OAI.MUB6.Certificate.GramRows.key747` and 889 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block16`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block51`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_MixedSemantics_Values15`, `MutuallyUnbiased_MixedSemantics_Values19`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D143`, `OAIQ106D144`, `OAIQ106D145`, `OAIQ106D146`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D162`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D167`, `OAIQ106D168`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D174`, `OAIQ106D176`, `OAIQ106D179`, `OAIQ106D180`, `OAIQ106D181`, `OAIQ106D182`, `OAIQ106D183`, `OAIQ106D184`, `OAIQ106D185` and `OAIQ106D186`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key22 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key34 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 1), (1, 2), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key235 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key247 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1315 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key1318 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (2, 1)]⟩
def key1350 : Key := ⟨0, 1, [(-2, -2), (-1, 2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1423 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (2, 2)]⟩
def key1426 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 0), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1764 : Key := ⟨0, 1, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1805 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 2)]⟩
def key1808 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 1)]⟩
def key1829 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key1893 : Key := ⟨0, 1, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 1)]⟩
def key1895 : Key := ⟨0, 1, [(-2, 2), (-1, -2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩
def key1915 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 1)]⟩
def key1918 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1929 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2077 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key256 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key301 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key315 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key326 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2584 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2635 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2721 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2845 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2988 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key746 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 0), (2, 1)]⟩
def key747 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key751 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key840 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 0), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key935 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -2)]⟩
def key964 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -1), (0, 0), (0, 0), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1241 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, -2), (2, 1)]⟩
def key1242 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key1251 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1252 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1255 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1258 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1260 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1264 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key1267 : Key := ⟨0, 1, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 1)]⟩
def key1270 : Key := ⟨0, 1, [(-2, -3), (-1, 2), (0, 0), (0, 0), (1, 0), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row700 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row701 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row702 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row703 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row704 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

def row705 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

def row712 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row713 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row714 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row715 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row716 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row717 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row730 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row731 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row732 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row733 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row734 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row735 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row742 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row743 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row744 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row745 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row746 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row747 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row760 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row761 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row762 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row763 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row764 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row765 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2809 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2810 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2811 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2812 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2813 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2814 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

def row2815 : Integer.Sparse Key := [(key1531, 1), (key1536, -1), (key1609, -1), (key1642, 1), (key1651, 1), (key1674, -1), (key1765, 1), (key1768, -1), (key1806, -1), (key1832, 1), (key1837, 1), (key1848, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2816 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2817 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2818 : Integer.Sparse Key := [(key2428, -4), (key2430, 4), (key2496, 4), (key2510, -4), (key2574, -4), (key2577, 4)]

def row2819 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2820 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2821 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2496, -4), (key2510, 4), (key2574, 4), (key2577, -4)]

def row2822 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2823 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2824 : Integer.Sparse Key := [(key2428, 4), (key2430, -4), (key2510, 6), (key2577, -6), (key3132, -4), (key3140, 4), (key3145, -2), (key3148, 2)]

def row2825 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2826 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2827 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2828 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2829 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2830 : Integer.Sparse Key := [(key2428, -6), (key2430, 4), (key2444, -2), (key2510, -2), (key3040, 4), (key3042, -2), (key3044, 2), (key3132, 2), (key3140, -2), (key3148, 2)]

def row2840 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2842 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2843 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2844 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2845 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2846 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2847 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2848 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1265, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1648, 2), (key1651, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -2)]

def row2849 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2850 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2851 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2852 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2853 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2854 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1265, 1), (key1268, 1), (key1531, 1), (key1536, 1), (key1648, -1), (key1651, -1), (key1765, -1), (key1768, -1), (key1806, 1), (key1809, 1)]

def row2855 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2856 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2857 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1536, 2), (key1648, -2), (key1651, -2), (key1765, -2), (key1768, -2), (key1806, 2), (key1809, 2)]

def row2858 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2859 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2860 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2861 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2862 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2863 : Integer.Sparse Key := [(key1256, 1), (key1261, 1), (key1265, -1), (key1268, -1), (key1531, -1), (key1536, -1), (key1648, 1), (key1651, 1), (key1765, 1), (key1768, 1), (key1806, -1), (key1809, -1)]

def row2864 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2865 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2866 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2867 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2868 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2869 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2870 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2871 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2872 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2873 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2874 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2875 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2876 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2877 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2878 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2879 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2880 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2881 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2882 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2883 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2884 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2885 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2886 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2887 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2888 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2889 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2890 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2891 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2892 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2893 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2894 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2895 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2896 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2897 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

def row2898 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

def row2899 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

def row2900 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

def row2901 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

def row2902 : Integer.Sparse Key := [(key2382, 1), (key2395, 1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

def row2903 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2904 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2905 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2906 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

def row2907 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

def row2908 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2909 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2910 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2911 : Integer.Sparse Key := [(key2592, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3032 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3033 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3034 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3035 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3036 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3037 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3038 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3039 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3040 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3041 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3042 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3043 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3044 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3045 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3046 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3047 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3048 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3049 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3050 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3051 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3052 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3053 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3054 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3055 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3056 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3057 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3058 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3059 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3060 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3061 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3062 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3063 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3064 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3065 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3066 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3067 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3068 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3069 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3070 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3071 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3072 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3073 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3074 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3075 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3076 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3077 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3078 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3079 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3080 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3081 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3082 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3083 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3084 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3085 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3086 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3087 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3088 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3089 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3090 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3091 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3092 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3093 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3094 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3095 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3096 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3097 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3098 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3099 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3100 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3101 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3102 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3103 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3104 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3105 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3106 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3107 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3108 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3109 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3110 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3111 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3112 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3113 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3114 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3115 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3116 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3117 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3118 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3119 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3120 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3121 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3122 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3123 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3124 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3125 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3126 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3127 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3128 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3129 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3130 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3131 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3132 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3133 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3134 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3135 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3136 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3137 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3138 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3139 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3140 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3141 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3142 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3143 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3144 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3145 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3146 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3147 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3148 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3149 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3150 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3151 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3152 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3153 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3154 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3155 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3156 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3157 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3158 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3159 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3160 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3161 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3162 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3163 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3164 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3165 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3166 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3167 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3168 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3169 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3170 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3171 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3172 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3173 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3174 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3175 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3212 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3213 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3214 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3227 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3228 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3229 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3266 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3267 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3268 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3269 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3270 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3271 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3272 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3273 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3274 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3275 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3276 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3277 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3278 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3279 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3280 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3281 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3282 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3283 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3284 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3285 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3286 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3287 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3288 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3289 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3290 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3291 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3292 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3293 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3294 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3295 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3296 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3297 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3298 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3299 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3300 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3301 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3302 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3303 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3304 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3317 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3318 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3319 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3320 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

def row3321 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

def row3322 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

def row3323 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

def row3324 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2)]

def row3325 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2)]

def row3326 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3327 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3328 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3329 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3330 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3331 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3332 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3333 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3334 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3335 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3336 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3337 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3338 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3339 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3340 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3341 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3342 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3343 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3344 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3345 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3346 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3347 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3348 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3349 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3350 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3351 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3352 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3353 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3354 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3355 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3356 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3357 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3358 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3359 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3360 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3361 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3362 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3363 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3364 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3365 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3366 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3367 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3368 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3369 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3370 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3371 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3372 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3373 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3374 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3375 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3376 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3377 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3378 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3379 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3380 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3381 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3382 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3383 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3384 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3385 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3386 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3387 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3388 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3389 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3390 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3391 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3392 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3393 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3394 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3395 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3396 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3397 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3398 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3399 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3400 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3401 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3402 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3403 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3404 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3405 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3406 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3407 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3408 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3409 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3410 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3411 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3412 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3413 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3414 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3415 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3416 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3417 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3418 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3419 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3420 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3421 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3422 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3423 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3424 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3425 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3426 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3427 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3428 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3429 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3430 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3431 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3432 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3433 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3434 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3435 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3436 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3437 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3438 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3439 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3440 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3441 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3442 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3443 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3444 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3445 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3446 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3447 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3448 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3449 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3452 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3453 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3454 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3462 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3463 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3466 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3467 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3468 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3469 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3473 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3474 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3475 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3476 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3477 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3478 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3480 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3481 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3482 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3483 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3484 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3488 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3489 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3490 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3491 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3492 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3493 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3494 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3495 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3496 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3497 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3498 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3499 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3500 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3501 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3502 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3503 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3504 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3505 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3506 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3507 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3508 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3509 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3510 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3511 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3512 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3513 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3514 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3515 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3516 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3517 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3518 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3519 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3520 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3521 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3522 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3523 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3524 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3525 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3526 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3527 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3528 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3529 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3530 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3531 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3532 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3533 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3534 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3535 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3536 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3537 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3538 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3539 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3540 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3541 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3542 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3543 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3544 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3545 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3546 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3547 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3548 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3549 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3550 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3551 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3552 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3553 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3554 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3555 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3556 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3557 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3558 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3559 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3560 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3561 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3562 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3563 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3564 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3565 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3566 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3567 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3568 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3569 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3570 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3571 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3572 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3573 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3574 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3575 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3576 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3577 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3578 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3579 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3580 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3581 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row3582 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row3583 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3584 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3585 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3586 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3587 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3588 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3589 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3590 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3591 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3592 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3593 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3594 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3595 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3596 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3597 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3598 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3599 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3600 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3601 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3602 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3603 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3604 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3605 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3606 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3607 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3608 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3609 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3610 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3611 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3612 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3613 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3614 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3615 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3616 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3617 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3618 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3619 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3620 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3621 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3622 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3623 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3624 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3625 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3626 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3627 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3628 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3629 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3630 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3631 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3633 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3634 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3635 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3636 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3637 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3638 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3639 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3640 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3641 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3642 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3643 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3644 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3645 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3646 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3647 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3648 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3649 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3650 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3651 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3652 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3653 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3654 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3655 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3656 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3657 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3658 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3659 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3660 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3661 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3662 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3663 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3664 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3665 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3666 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3667 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3668 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3669 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3670 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3671 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3672 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3673 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3674 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3675 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3676 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3677 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3678 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3679 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3680 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3681 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3682 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3683 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3684 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3685 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3687 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3688 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3689 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3690 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3691 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3692 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3693 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3694 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3695 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3696 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3697 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3698 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3699 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3700 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3701 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3702 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3703 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3710 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

def row3711 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3712 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

def row3725 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3726 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3727 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3734 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3735 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3736 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3737 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3738 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3739 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3740 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3741 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3742 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3743 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3744 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3745 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3746 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3747 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3748 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3749 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3750 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3751 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3752 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3753 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3754 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3755 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3756 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3757 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3758 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3759 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3760 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3761 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3762 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3763 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4004 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4005 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4006 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4007 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4008 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4009 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4010 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4011 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4012 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4013 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4014 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4015 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4016 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4017 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4018 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4019 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4020 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4021 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4022 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4023 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4024 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4025 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4026 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4027 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4028 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4029 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4030 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4031 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4032 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4033 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4034 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4035 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4036 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4037 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4038 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4039 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4040 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4041 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4042 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4043 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4044 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4045 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4046 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4047 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4048 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4049 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4050 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4051 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4052 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4053 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4054 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4055 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4056 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4057 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4058 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4059 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4060 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4061 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4062 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4063 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4064 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4065 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4066 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4067 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4068 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4069 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4070 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4071 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4072 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4073 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4074 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4075 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4076 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4077 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4078 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4079 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4080 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4081 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4082 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4083 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4084 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4085 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4086 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4087 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4088 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4089 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4090 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4091 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4092 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4093 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4094 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4095 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4096 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4097 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4098 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4099 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4100 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4101 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4102 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4103 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4104 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4105 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4106 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4107 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4108 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4109 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4110 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4111 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4112 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4113 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4114 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4115 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4116 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4117 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4118 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4119 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4120 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4121 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4122 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4123 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4124 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4125 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4126 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4127 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4128 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4129 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4130 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4131 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4132 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4133 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4134 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4135 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4136 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4137 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4138 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4139 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4140 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4141 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4142 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4143 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4144 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1009 : Sparse Master := [(Sum.inr 1009, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1219 : Sparse Master := [(Sum.inr 1219, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


