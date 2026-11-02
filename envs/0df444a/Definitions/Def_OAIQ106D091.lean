-- Prove2me | Definitions.Def_OAIQ106D091
-- name    : OAIQ106D091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:55:21.255832+00:00
-- url     : https://prove2.me/theorems/37683759-ded0-415d-8511-4c66147c83d0
-- title:
--   Definitions bundle OAIQ106D091 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 965 declarations of OpenAI's Lean: 965 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key1046`, `OAI.MUB6.Certificate.GramRows.key1056`, `OAI.MUB6.Certificate.GramRows.key1060`, `OAI.MUB6.Certificate.GramRows.key1079`, `OAI.MUB6.Certificate.GramRows.key1253`, `OAI.MUB6.Certificate.GramRows.key1282`, `OAI.MUB6.Certificate.GramRows.key1403`, `OAI.MUB6.Certificate.GramRows.key1412`, `OAI.MUB6.Certificate.GramRows.key1499`, `OAI.MUB6.Certificate.GramRows.key1509`, `OAI.MUB6.Certificate.GramRows.key1636`, `OAI.MUB6.Certificate.GramRows.key1946`, `OAI.MUB6.Certificate.GramRows.key1949`, `OAI.MUB6.Certificate.GramRows.key208`, `OAI.MUB6.Certificate.GramRows.key2199`, `OAI.MUB6.Certificate.GramRows.key229`, `OAI.MUB6.Certificate.GramRows.key2425`, `OAI.MUB6.Certificate.GramRows.key2442`, `OAI.MUB6.Certificate.GramRows.key2582`, `OAI.MUB6.Certificate.GramRows.key2590`, `OAI.MUB6.Certificate.GramRows.key2690`, `OAI.MUB6.Certificate.GramRows.key296`, `OAI.MUB6.Certificate.GramRows.key3031`, `OAI.MUB6.Certificate.GramRows.key3032`, `OAI.MUB6.Certificate.GramRows.key3046`, `OAI.MUB6.Certificate.GramRows.key3080`, `OAI.MUB6.Certificate.GramRows.key3100`, `OAI.MUB6.Certificate.GramRows.key373`, `OAI.MUB6.Certificate.GramRows.key456`, `OAI.MUB6.Certificate.GramRows.key5`, `OAI.MUB6.Certificate.GramRows.key550`, `OAI.MUB6.Certificate.GramRows.key8`, `OAI.MUB6.Certificate.GramRows.key980`, `OAI.MUB6.Certificate.GramRows.key990`, `OAI.MUB6.Certificate.GramRows.row10694`, `OAI.MUB6.Certificate.GramRows.row10695`, `OAI.MUB6.Certificate.GramRows.row10696`, `OAI.MUB6.Certificate.GramRows.row10697`, `OAI.MUB6.Certificate.GramRows.row10698`, `OAI.MUB6.Certificate.GramRows.row10699` and 925 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block19`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block107`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_GramRows_Block99`, `MutuallyUnbiased_MixedSemantics_Values73`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D155`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D165`, `OAIQ106D167`, `OAIQ106D168`, `OAIQ106D184` and `OAIQ106D186`.
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

def key5 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key8 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 0), (1, 3)]⟩

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

def key208 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key229 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 3), (1, 0), (1, 0)]⟩

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

def key1282 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key1403 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 1), (3, 2)]⟩

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

def key1412 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1499 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key1509 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 3), (1, -1), (1, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1636 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩

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

def key1946 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, 0), (0, 1), (2, -1)]⟩
def key1949 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2199 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2425 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2442 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩

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

def key296 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 2), (1, 0), (1, 0)]⟩
def key373 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0)]⟩

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

def key2582 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2590 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (1, 0), (1, 0), (1, 3)]⟩

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

def key2690 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩

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

def key3031 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩
def key3032 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 0), (2, 3)]⟩
def key3046 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key3080 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 0), (2, 3)]⟩
def key3100 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, -1), (2, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key456 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key550 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (0, 1), (2, -2)]⟩

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

def key980 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key990 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 1), (3, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1046 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (0, 1), (3, 2)]⟩
def key1056 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key1060 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 2), (2, -1)]⟩
def key1079 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩

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

def key1253 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9728 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9730 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9731 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9732 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3017, 2), (key3030, 2)]

def row9733 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

def row9734 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

def row9735 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9736 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9737 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9738 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9739 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9740 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9837 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9838 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9839 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9840 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9841 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9842 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9843 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9844 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9845 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9846 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9847 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9848 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

def row9849 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9850 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9851 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9852 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9853 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9854 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9855 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9856 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9857 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9858 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9859 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9860 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

def row9861 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9862 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9863 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9864 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9865 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9866 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9867 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9868 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9869 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9870 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9871 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9872 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2770, -12), (key2773, -6), (key2847, 4), (key2878, 4), (key2881, 4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row9873 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9874 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9875 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9876 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9877 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9878 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9879 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9880 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9881 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9882 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9883 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9884 : Integer.Sparse Key := [(key2591, 4), (key2601, 2), (key2770, 4), (key2847, -12), (key2878, 4), (key2890, -6), (key2911, 4), (key2932, 2), (key2969, -6), (key2990, 4)]

def row9885 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9886 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9887 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9888 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9889 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9890 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9891 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9892 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9893 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9894 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9895 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9896 : Integer.Sparse Key := [(key2615, 6), (key2670, -6), (key2785, -6), (key2793, -12), (key2808, 6), (key2828, 12)]

def row9897 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9898 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9899 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9900 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9901 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9902 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9903 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9904 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9905 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9906 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9907 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9908 : Integer.Sparse Key := [(key2631, 6), (key2705, -6), (key2785, 6), (key2808, -6), (key2859, -12), (key2869, 12)]

def row9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9910 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9911 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9912 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9913 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9914 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -8), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9915 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9916 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9917 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9918 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -6), (key2952, -2), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9919 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9920 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2707, 2), (key2730, 4), (key2810, -2), (key2833, -4), (key2952, -4), (key2962, -4), (key2964, -4), (key2978, 4), (key2985, 4), (key2994, 4)]

def row9921 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9922 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9923 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9924 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9925 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9926 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 8), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9927 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9928 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9929 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9930 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 6), (key2945, 2), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9931 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

def row9932 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, 2), (key2707, -2), (key2730, -4), (key2749, 4), (key2945, 4), (key2962, 4), (key2978, -4), (key2985, -4), (key2994, -4), (key3004, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10694 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10695 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10696 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10697 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10698 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10699 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10700 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10701 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10702 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10703 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10704 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10705 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10706 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10707 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10708 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10709 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10710 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10711 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10712 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10713 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10714 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10715 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10716 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10717 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10718 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10719 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10720 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10721 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10722 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10723 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10724 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10725 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10726 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10727 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10728 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10729 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10874 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10875 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10876 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10877 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10878 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10879 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10880 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10881 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10882 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10883 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10884 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10885 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10886 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10887 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10888 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10889 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10890 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10891 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10892 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10893 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10894 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10895 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10896 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10897 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10898 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10899 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10900 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10901 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10902 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10903 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10904 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10905 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10906 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10907 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10908 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10909 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10946 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10947 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10948 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10949 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10950 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10951 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10952 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10953 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10954 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10955 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10956 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10957 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10958 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10959 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10960 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10961 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10962 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10963 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10964 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10965 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10966 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10967 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10968 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10969 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10970 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10971 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10972 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10973 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10974 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10975 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10976 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10977 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10978 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10979 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10980 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10981 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10982 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10983 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10984 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10985 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10986 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10987 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10988 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10989 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10990 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10991 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10992 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10993 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10994 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10995 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10996 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10997 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10998 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10999 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11000 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11001 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11002 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11003 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11004 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11005 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11006 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11007 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11008 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11009 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11010 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11011 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11012 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11013 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11014 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11015 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11016 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11017 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11018 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11019 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11020 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11021 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11022 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11023 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11024 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11025 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11026 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11027 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11028 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11029 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11030 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11031 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11038 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11039 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11040 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11041 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11042 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11043 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11044 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11045 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11046 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11047 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11048 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11049 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11050 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11051 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11052 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11053 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11114 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11115 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11116 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11117 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11118 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11119 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11120 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

def row11121 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

def row11122 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

def row11123 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

def row11124 : Integer.Sparse Key := [(key2370, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6)]

def row11125 : Integer.Sparse Key := [(key2398, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6)]

def row11126 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11127 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11128 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11129 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11130 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11131 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11132 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11133 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11134 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11135 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11136 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11137 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11138 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11139 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11140 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11141 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11142 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11143 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11144 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11145 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11146 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11147 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11148 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11149 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11150 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11151 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11152 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11153 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11154 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11155 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11156 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11157 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11158 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11159 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11160 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11161 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11198 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11199 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11200 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11201 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11202 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11203 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11204 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11205 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11206 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11207 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11208 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11209 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11210 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11211 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11212 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11213 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11214 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11215 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11216 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11217 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11218 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11219 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11220 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11221 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11222 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11223 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11224 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11225 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11226 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11227 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11228 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11229 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11230 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11231 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11232 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11233 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11270 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11271 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11272 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11273 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11274 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11275 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11276 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11277 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11278 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11279 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11280 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11281 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11282 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11283 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11284 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11285 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11286 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11287 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11288 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11289 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11290 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11291 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11292 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11293 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11294 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11295 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11296 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11297 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11298 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11299 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11300 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11301 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11302 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11303 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11304 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11305 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11306 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11307 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11308 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11309 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11310 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11311 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11312 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11313 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11314 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11315 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11316 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11317 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11318 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11319 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11320 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11321 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11322 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11323 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11324 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11325 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11326 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11327 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11328 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11329 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11330 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11331 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11332 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11333 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11334 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11335 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11336 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11337 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11338 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11339 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11340 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11341 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11450 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11451 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11452 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11453 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11454 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11455 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11456 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11457 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11458 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11459 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11460 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11461 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11462 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11463 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11464 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11465 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11466 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11467 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11468 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11469 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11470 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11471 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11472 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11473 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11474 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11475 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11476 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11477 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11478 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11479 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11480 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11481 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11482 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11483 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11484 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11485 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11486 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11487 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11488 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11489 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11490 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11491 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11492 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11493 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11494 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11495 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11496 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11497 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11547 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11548 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11549 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11550 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11551 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11552 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11553 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11554 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11555 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11556 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11557 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11570 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11571 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11572 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11573 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11574 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11575 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11576 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11577 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11578 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11579 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11580 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11581 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11583 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11584 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11585 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11586 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11587 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11588 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11589 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11590 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11591 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11592 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11593 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11594 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11595 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11596 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11597 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11598 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11599 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11600 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11601 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11602 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11603 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11604 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11605 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11619 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11620 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11622 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11623 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11624 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11625 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11626 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11627 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11628 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11629 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11630 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11631 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11632 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11633 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11634 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11635 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11636 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11637 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11638 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11639 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11640 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11641 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11654 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11655 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11656 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11657 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11658 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11659 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11660 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11661 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11662 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11663 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11664 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11665 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11678 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11679 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11680 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11681 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11682 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11683 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11684 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11685 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11686 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11687 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11688 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11689 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11690 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11691 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11692 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11693 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11694 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11695 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11696 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11697 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11698 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11699 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11700 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11701 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11738 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11739 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11740 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11741 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11742 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11743 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11744 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11745 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11746 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11747 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11748 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11749 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11751 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11752 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11753 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11754 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11755 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11756 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11757 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11758 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11759 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11760 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11761 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11762 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11763 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11764 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11765 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11766 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11767 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11768 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11769 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11770 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11771 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11772 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11773 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11774 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11775 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11776 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11777 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11778 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11779 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11780 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11781 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11782 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11783 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11784 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11785 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11786 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11787 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11788 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11789 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11790 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11791 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11864 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11865 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11866 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11867 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11868 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11869 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11870 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11871 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11872 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11873 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2437, 2), (key2443, 2), (key2524, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2966, -2), (key2968, -4), (key2989, -2)]

def row11874 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

def row11875 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

def row11876 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11877 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11878 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11879 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11880 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11881 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11900 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11901 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11902 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11903 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11904 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11905 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11906 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11907 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11908 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11909 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11910 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11911 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11912 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11913 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11914 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11915 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11916 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11917 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11918 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11919 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11920 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11921 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11922 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11923 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11924 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11926 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11927 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11928 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11929 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11930 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11931 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11932 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11933 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11934 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11935 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11936 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11937 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11938 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11939 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11940 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11941 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11942 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11943 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11944 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11945 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2394, -2), (key2411, -2), (key2437, 2), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2580, 2), (key2587, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2966, 2), (key2989, 2)]

def row11946 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

def row11947 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

def row11948 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11949 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11950 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11951 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11952 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11953 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11972 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11973 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11974 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11975 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11976 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11977 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11978 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11979 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11980 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11981 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11982 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11983 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11984 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11985 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11986 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11987 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11988 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11989 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row12026 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12027 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12028 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12029 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12030 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12031 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12032 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12033 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12034 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12035 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12036 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12037 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12038 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12039 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12040 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12041 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12042 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12043 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12062 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12063 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12064 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12065 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12066 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12067 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12068 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12069 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12070 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12071 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12072 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12073 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12074 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12075 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12076 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12077 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12078 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12079 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12080 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12081 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12082 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12083 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12084 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12085 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12086 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12087 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12088 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12089 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12090 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12091 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12092 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

def row12093 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

def row12094 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12095 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12096 : Integer.Sparse Key := [(key2379, 2), (key2407, 2), (key2592, -2), (key2595, -4), (key2602, 4), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12097 : Integer.Sparse Key := [(key2595, -4), (key2602, 4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12152 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12153 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12154 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12155 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12156 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12157 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12158 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12159 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12160 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12161 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12162 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12163 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12164 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12165 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12166 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12167 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12168 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12169 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12170 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12171 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12172 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12173 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12174 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12175 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12176 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12178 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12179 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12180 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12181 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12182 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12183 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12184 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12185 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12186 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12187 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7574 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7575 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7576 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7577 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7578 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7579 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7580 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7581 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7582 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7583 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7584 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7585 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9597 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9598 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9599 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9600 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9601 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9602 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9603 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9604 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9605 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9606 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9607 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9608 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

def row9609 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9610 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9611 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

def row9612 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9613 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9614 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

def row9615 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9616 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9617 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9618 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9619 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9620 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

def row9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9622 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9623 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9624 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -4), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9625 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9626 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9627 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9628 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9629 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9630 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9631 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9632 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9633 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9634 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9635 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

def row9636 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3017, 2), (key3030, 2)]

def row9637 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

def row9638 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

def row9639 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9640 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9641 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9642 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9643 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9644 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

def row9669 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9670 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9671 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

def row9672 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 4), (key2831, 2), (key2835, 4), (key3017, 4)]

def row9673 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

def row9674 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

def row9675 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9676 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9677 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9678 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9679 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9680 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

def row9681 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9682 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9683 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9684 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9685 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9686 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9687 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9688 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9689 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9690 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9691 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9692 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

def row9717 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9718 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9719 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9720 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9721 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9722 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9723 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9724 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9725 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9726 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row9727 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4708 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


