-- Prove2me | Definitions.Def_OAIQ106D152
-- name    : OAIQ106D152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:59:53.606132+00:00
-- url     : https://prove2.me/theorems/7fc921b9-b367-4e8b-a79f-3cbf4b82d290
-- title:
--   Definitions bundle OAIQ106D152 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1378 declarations of OpenAI's Lean: 1378 definitions. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block4.terms1`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms18`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms19`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms20`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms21`, `OAI.MUB6.Certificate.GramRows.row13205`, `OAI.MUB6.Certificate.GramRows.row13206`, `OAI.MUB6.Certificate.GramRows.row13207`, `OAI.MUB6.Certificate.GramRows.row13208`, `OAI.MUB6.Certificate.GramRows.row13209`, `OAI.MUB6.Certificate.GramRows.row13210`, `OAI.MUB6.Certificate.GramRows.row13211`, `OAI.MUB6.Certificate.GramRows.row13212`, `OAI.MUB6.Certificate.GramRows.row13213`, `OAI.MUB6.Certificate.GramRows.row13214`, `OAI.MUB6.Certificate.GramRows.row13215`, `OAI.MUB6.Certificate.GramRows.row13216`, `OAI.MUB6.Certificate.GramRows.row13217`, `OAI.MUB6.Certificate.GramRows.row13218`, `OAI.MUB6.Certificate.GramRows.row13219`, `OAI.MUB6.Certificate.GramRows.row13220`, `OAI.MUB6.Certificate.GramRows.row13221`, `OAI.MUB6.Certificate.GramRows.row13222`, `OAI.MUB6.Certificate.GramRows.row13223`, `OAI.MUB6.Certificate.GramRows.row13224`, `OAI.MUB6.Certificate.GramRows.row13225`, `OAI.MUB6.Certificate.GramRows.row13226`, `OAI.MUB6.Certificate.GramRows.row13227`, `OAI.MUB6.Certificate.GramRows.row13228`, `OAI.MUB6.Certificate.GramRows.row13229`, `OAI.MUB6.Certificate.GramRows.row13230`, `OAI.MUB6.Certificate.GramRows.row13231`, `OAI.MUB6.Certificate.GramRows.row13232`, `OAI.MUB6.Certificate.GramRows.row13233`, `OAI.MUB6.Certificate.GramRows.row13234`, `OAI.MUB6.Certificate.GramRows.row13235`, `OAI.MUB6.Certificate.GramRows.row13236`, `OAI.MUB6.Certificate.GramRows.row13237`, `OAI.MUB6.Certificate.GramRows.row13238`, `OAI.MUB6.Certificate.GramRows.row13239` and 1338 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block155`, `MutuallyUnbiased_GramRows_Block156`, `MutuallyUnbiased_GramRows_Block157`, `MutuallyUnbiased_GramRows_Block158`, `MutuallyUnbiased_GramRows_Block159`, `MutuallyUnbiased_GramRows_Block160`, `MutuallyUnbiased_GramRows_Block161`, `MutuallyUnbiased_GramRows_Block162`, `MutuallyUnbiased_GramRows_Block163`, `MutuallyUnbiased_GramRows_Block164`, `MutuallyUnbiased_GramRows_Block166`, `MutuallyUnbiased_GramRows_Block167`.
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block4

def terms1 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 0, 2], -2⟩,
  ⟨0, ![1, -3, 0, 0, 2, 0], -2⟩,
  ⟨0, ![1, -3, 0, 2, 0, 0], -2⟩,
  ⟨0, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨0, ![1, 0, -3, 0, 0, 2], -2⟩,
  ⟨0, ![1, 0, -3, 0, 2, 0], -2⟩,
  ⟨0, ![1, 0, -3, 2, 0, 0], -2⟩,
  ⟨0, ![1, 0, 0, -3, 0, 2], 2⟩,
  ⟨0, ![1, 0, 0, -3, 2, 0], 2⟩,
  ⟨0, ![1, 0, 0, 0, -3, 2], 2⟩,
  ⟨0, ![1, 0, 0, 0, 2, -3], 2⟩,
  ⟨0, ![1, 0, 0, 2, -3, 0], 2⟩,
  ⟨0, ![1, 0, 0, 2, 0, -3], 2⟩,
  ⟨0, ![1, 0, 2, -3, 0, 0], -2⟩,
  ⟨0, ![1, 0, 2, 0, -3, 0], -2⟩,
  ⟨0, ![1, 0, 2, 0, 0, -3], -2⟩,
  ⟨0, ![1, 2, -3, 0, 0, 0], 6⟩,
  ⟨0, ![1, 2, 0, -3, 0, 0], -2⟩,
  ⟨0, ![1, 2, 0, 0, -3, 0], -2⟩,
  ⟨0, ![1, 2, 0, 0, 0, -3], -2⟩
]

def terms18 : Array TaggedTerm := #[
  ⟨0, ![1, -1, -1, -1, 0, 2], -2⟩,
  ⟨0, ![1, -1, -1, -1, 2, 0], -2⟩,
  ⟨0, ![1, -1, -1, 0, -1, 2], -2⟩,
  ⟨0, ![1, -1, -1, 0, 2, -1], -2⟩,
  ⟨0, ![1, -1, -1, 2, -1, 0], -2⟩,
  ⟨0, ![1, -1, -1, 2, 0, -1], -2⟩,
  ⟨0, ![1, -1, 0, -1, -1, 2], 2⟩,
  ⟨0, ![1, -1, 0, -1, 2, -1], 2⟩,
  ⟨0, ![1, -1, 0, 2, -1, -1], 2⟩,
  ⟨0, ![1, -1, 2, -1, -1, 0], 2⟩,
  ⟨0, ![1, -1, 2, -1, 0, -1], 2⟩,
  ⟨0, ![1, -1, 2, 0, -1, -1], 2⟩,
  ⟨0, ![1, 0, -1, -1, -1, 2], 2⟩,
  ⟨0, ![1, 0, -1, -1, 2, -1], 2⟩,
  ⟨0, ![1, 0, -1, 2, -1, -1], 2⟩,
  ⟨0, ![1, 0, 2, -1, -1, -1], -6⟩,
  ⟨0, ![1, 2, -1, -1, -1, 0], 2⟩,
  ⟨0, ![1, 2, -1, -1, 0, -1], 2⟩,
  ⟨0, ![1, 2, -1, 0, -1, -1], 2⟩,
  ⟨0, ![1, 2, 0, -1, -1, -1], -6⟩
]

def terms19 : Array TaggedTerm := #[
  ⟨0, ![-2, 0, 0, 0, 1, 1], 4⟩,
  ⟨0, ![-2, 0, 0, 1, 0, 1], 4⟩,
  ⟨0, ![-2, 0, 0, 1, 1, 0], 4⟩,
  ⟨0, ![-2, 0, 1, 0, 0, 1], -4⟩,
  ⟨0, ![-2, 0, 1, 0, 1, 0], -4⟩,
  ⟨0, ![-2, 0, 1, 1, 0, 0], -4⟩,
  ⟨0, ![-2, 1, 0, 0, 0, 1], -4⟩,
  ⟨0, ![-2, 1, 0, 0, 1, 0], -4⟩,
  ⟨0, ![-2, 1, 0, 1, 0, 0], -4⟩,
  ⟨0, ![-2, 1, 1, 0, 0, 0], 12⟩
]

def terms20 : Array TaggedTerm := #[
  ⟨0, ![1, -1, -1, 0, 0, 1], 4⟩,
  ⟨0, ![1, -1, -1, 0, 1, 0], 4⟩,
  ⟨0, ![1, -1, -1, 1, 0, 0], 4⟩,
  ⟨0, ![1, -1, 0, -1, 0, 1], -2⟩,
  ⟨0, ![1, -1, 0, -1, 1, 0], -2⟩,
  ⟨0, ![1, -1, 0, 0, -1, 1], -2⟩,
  ⟨0, ![1, -1, 0, 0, 1, -1], -2⟩,
  ⟨0, ![1, -1, 0, 1, -1, 0], -2⟩,
  ⟨0, ![1, -1, 0, 1, 0, -1], -2⟩,
  ⟨0, ![1, 0, -1, -1, 0, 1], -2⟩,
  ⟨0, ![1, 0, -1, -1, 1, 0], -2⟩,
  ⟨0, ![1, 0, -1, 0, -1, 1], -2⟩,
  ⟨0, ![1, 0, -1, 0, 1, -1], -2⟩,
  ⟨0, ![1, 0, -1, 1, -1, 0], -2⟩,
  ⟨0, ![1, 0, -1, 1, 0, -1], -2⟩,
  ⟨0, ![1, 0, 0, -1, -1, 1], 4⟩,
  ⟨0, ![1, 0, 0, -1, 1, -1], 4⟩,
  ⟨0, ![1, 0, 0, 1, -1, -1], 4⟩
]

def terms21 : Array TaggedTerm := #[
  ⟨1, ![2, -1, -1, -1, 0, 1], -2⟩,
  ⟨1, ![2, -1, -1, -1, 1, 0], -2⟩,
  ⟨1, ![2, -1, -1, 0, -1, 1], -2⟩,
  ⟨1, ![2, -1, -1, 0, 1, -1], -2⟩,
  ⟨1, ![2, -1, -1, 1, -1, 0], -2⟩,
  ⟨1, ![2, -1, -1, 1, 0, -1], -2⟩,
  ⟨1, ![2, -1, 0, -1, -1, 1], 2⟩,
  ⟨1, ![2, -1, 0, -1, 1, -1], 2⟩,
  ⟨1, ![2, -1, 0, 1, -1, -1], 2⟩,
  ⟨1, ![2, -1, 1, -1, -1, 0], 2⟩,
  ⟨1, ![2, -1, 1, -1, 0, -1], 2⟩,
  ⟨1, ![2, -1, 1, 0, -1, -1], 2⟩,
  ⟨1, ![2, 0, -1, -1, -1, 1], 2⟩,
  ⟨1, ![2, 0, -1, -1, 1, -1], 2⟩,
  ⟨1, ![2, 0, -1, 1, -1, -1], 2⟩,
  ⟨1, ![2, 0, 1, -1, -1, -1], -6⟩,
  ⟨1, ![2, 1, -1, -1, -1, 0], 2⟩,
  ⟨1, ![2, 1, -1, -1, 0, -1], 2⟩,
  ⟨1, ![2, 1, -1, 0, -1, -1], 2⟩,
  ⟨1, ![2, 1, 0, -1, -1, -1], -6⟩
]

end MUB6.Certificate.GramFunctions.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13205 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13206 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13207 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13208 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

def row13209 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13210 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13211 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13212 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13213 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13214 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13215 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13216 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13217 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

def row13218 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13219 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13220 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13221 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

def row13222 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13223 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13224 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

def row13225 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13226 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13227 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13228 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

def row13229 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13230 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13231 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13232 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13233 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13234 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

def row13235 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

def row13236 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13237 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

def row13238 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13239 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13240 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

def row13241 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

def row13242 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13243 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

def row13244 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16743 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16744 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16745 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

def row16746 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16747 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16748 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16749 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16750 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16751 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16752 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16753 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16754 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16755 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16756 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16757 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

def row16758 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16759 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16760 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

def row16761 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16762 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16763 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

def row16764 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16765 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16766 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16767 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16768 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16769 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16770 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16771 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16772 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16773 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16774 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16775 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

def row16776 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16777 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16778 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

def row16779 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16780 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16781 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

def row16782 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16783 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16784 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16785 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16786 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16787 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16788 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16789 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16790 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16791 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16792 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16793 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

def row16794 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16795 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16796 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

def row16797 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16798 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16799 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

def row16800 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16801 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16802 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16803 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16804 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16805 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16806 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16807 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16808 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16809 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16810 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16811 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

def row16812 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16813 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16814 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

def row16815 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16816 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16817 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

def row16818 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16819 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16820 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16821 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16822 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16823 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16824 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16825 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16826 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16827 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16828 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16829 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

def row16830 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16831 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16832 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

def row16833 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16834 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16835 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

def row16837 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16838 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16839 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16840 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16841 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16842 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16843 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16844 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16845 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16846 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16847 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

def row16848 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16849 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16850 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

def row16851 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16852 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16853 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

def row16854 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16855 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16856 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16857 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16858 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16859 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16860 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16861 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16862 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16863 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16864 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16865 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

def row16866 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16867 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16868 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

def row16869 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16870 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16871 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

def row16872 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16873 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16874 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16875 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16876 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16877 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16878 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16879 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16880 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16881 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16882 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16883 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

def row16884 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

def row16885 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

def row16886 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16944 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16945 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16946 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16947 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16948 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16949 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16950 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16951 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16952 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16953 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16954 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16955 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

def row16956 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16957 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16958 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

def row16959 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16960 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16961 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

def row16962 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16963 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16964 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16965 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16966 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16967 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16968 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16969 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16970 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16971 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16972 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16973 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

def row16974 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16975 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16976 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

def row16977 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16978 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16979 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

def row16980 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16981 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16982 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16983 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16984 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16985 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16986 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16987 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16988 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16989 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16990 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16991 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

def row16992 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16993 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16994 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

def row16995 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16996 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16997 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

def row16998 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row16999 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17000 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17001 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17002 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17003 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17004 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17005 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17006 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17007 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17008 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17009 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

def row17010 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17011 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17012 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

def row17013 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17014 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17015 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

def row17016 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17017 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17018 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17019 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17020 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17021 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17022 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17023 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17025 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17026 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17027 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

def row17028 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17029 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17030 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

def row17031 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17032 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17033 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17034 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17035 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17036 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

def row17037 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17038 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17039 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17040 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17041 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17042 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17043 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17044 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17045 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17046 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

def row17047 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17048 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17049 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

def row17050 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

def row17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17052 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17053 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17054 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17055 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17056 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

def row17057 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17058 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17059 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17060 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17061 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17062 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

def row17063 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17064 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17065 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

def row17066 : Integer.Sparse Key := [(key54, -2), (key63, 12), (key122, 6), (key128, -6), (key199, -6), (key693, -4), (key697, -6), (key848, 6)]

def row17067 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17068 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17069 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

def row17070 : Integer.Sparse Key := [(key54, -2), (key56, -6), (key63, 12), (key122, 6), (key128, -6), (key198, 6), (key199, -6), (key693, -4)]

def row17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17072 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17073 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17074 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17075 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17076 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

def row17077 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17078 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17079 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17080 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17081 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17082 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17083 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17084 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17085 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17086 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

def row17087 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17088 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17089 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

def row17090 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

def row17091 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17092 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17093 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17094 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17095 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17096 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

def row17097 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17098 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17099 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17100 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17101 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17102 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17103 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17104 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17105 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17106 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

def row17107 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17108 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17109 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

def row17110 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

def row17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17112 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17113 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17114 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17115 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17116 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

def row17117 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17118 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17119 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17120 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17121 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17122 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17123 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17124 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17125 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17126 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

def row17127 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17128 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17129 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

def row17130 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

def row17131 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17132 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17133 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17134 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17135 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17136 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

def row17137 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17138 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17139 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17140 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17141 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17142 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17143 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17144 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17145 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

def row17146 : Integer.Sparse Key := [(key65, -12), (key82, 12), (key695, 12), (key700, -12)]

def row17147 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17148 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17149 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

def row17150 : Integer.Sparse Key := [(key58, 12), (key65, -12), (key68, -12), (key82, 12)]

def row17151 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17152 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17153 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17154 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17155 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17156 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

def row17157 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17158 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17159 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17160 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17161 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17162 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17163 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17164 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17165 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17166 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

def row17167 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17168 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17169 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

def row17170 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

def row17171 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17172 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17173 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17174 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17175 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17176 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

def row17177 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17178 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17179 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17180 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17181 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17182 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17183 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17184 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17185 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17186 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

def row17187 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17188 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17189 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

def row17190 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

def row17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17192 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17193 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17194 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17195 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17196 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

def row17197 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17198 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17199 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17200 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17201 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17202 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17203 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17204 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17205 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17206 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

def row17207 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17208 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17209 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

def row17210 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

def row17211 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17212 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17213 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17214 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17215 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17216 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

def row17217 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17218 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17219 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17220 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17221 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17222 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17223 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17224 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17225 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17226 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

def row17227 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17228 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17229 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

def row17230 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

def row17231 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17232 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17233 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17234 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17235 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17236 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

def row17237 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17238 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17239 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17240 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17241 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17242 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17243 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17244 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17245 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17246 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

def row17247 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17248 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17249 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

def row17250 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

def row17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17252 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17253 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17254 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17255 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17256 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

def row17257 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17258 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17259 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17260 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17261 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17262 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17263 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17264 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17265 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17266 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

def row17267 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17268 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17269 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

def row17270 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

def row17271 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17272 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17273 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17274 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17275 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17276 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

def row17277 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17278 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17279 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17280 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17281 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17282 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17283 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17284 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17285 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17286 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

def row17287 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17288 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17289 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

def row17290 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

def row17291 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17292 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17293 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17294 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17295 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17296 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

def row17297 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17298 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17299 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17300 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17301 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17302 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17303 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17304 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17305 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17306 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

def row17307 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17308 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17309 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

def row17310 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

def row17311 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17312 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17313 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17314 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17315 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17316 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

def row17317 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17318 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17319 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17320 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17321 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17322 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17323 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17324 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17325 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17326 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

def row17327 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17328 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17329 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

def row17330 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

def row17331 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17332 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17333 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17334 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17335 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17336 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

def row17337 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17338 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17339 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17340 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17341 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17342 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17343 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17344 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17345 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17346 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

def row17347 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17348 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17349 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

def row17350 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

def row17351 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17352 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17353 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17354 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17355 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17356 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

def row17357 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17358 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17359 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17360 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17361 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17362 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17363 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17364 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17365 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17366 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

def row17367 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17368 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17369 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

def row17370 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

def row17371 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17372 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17373 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17374 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17375 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17376 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

def row17377 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17378 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17379 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17380 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17381 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17382 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17383 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17384 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17385 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17386 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

def row17387 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17388 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17389 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

def row17390 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

def row17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17392 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17393 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

def row17394 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

def row17395 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17396 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

def row17397 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17398 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17399 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

def row17400 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17401 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17402 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

def row17403 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17404 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17405 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

def row17406 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 12), (key769, 6), (key793, -12)]

def row17407 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17408 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

def row17409 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

def row17410 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 6), (key768, 6), (key769, 6), (key793, -12)]

def row17411 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17412 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17413 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

def row17414 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17415 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17416 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17417 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17418 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17419 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

def row17420 : Integer.Sparse Key := [(key1854, 12), (key1856, -24), (key1858, 12)]

def row17421 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17422 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17423 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

def row17424 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17425 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17426 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17427 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17428 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17429 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

def row17430 : Integer.Sparse Key := [(key620, -12), (key624, 12), (key646, 12), (key652, -12)]

def row17431 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17432 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17433 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

def row17434 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17435 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17436 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17437 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17438 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17439 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

def row17440 : Integer.Sparse Key := [(key1853, -12), (key1857, 12), (key1885, 12), (key1888, -12)]

def row17441 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17442 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17443 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

def row17444 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17445 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17446 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17447 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17448 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17449 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

def row17450 : Integer.Sparse Key := [(key1959, 12), (key1961, -12), (key1967, -12), (key1970, 12)]

def row17451 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17452 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17453 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

def row17454 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17455 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17456 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17457 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17458 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17459 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

def row17460 : Integer.Sparse Key := [(key665, -12), (key666, 12), (key682, 12), (key683, -12)]

def row17461 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17462 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17463 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

def row17464 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17465 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17466 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17467 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17468 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17469 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

def row17470 : Integer.Sparse Key := [(key621, 12), (key623, -24), (key625, 12)]

def row17471 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17472 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17473 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

def row17474 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17475 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17476 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17477 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17478 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17479 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

def row17480 : Integer.Sparse Key := [(key1862, -12), (key1866, 12), (key1868, 12), (key1871, -12)]

def row17481 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17482 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17483 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

def row17484 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17485 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17486 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17487 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17488 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17489 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

def row17490 : Integer.Sparse Key := [(key1963, 12), (key1965, -24), (key1968, 12)]

def row17491 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17492 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17493 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

def row17494 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17495 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17496 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17497 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17498 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17499 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

def row17500 : Integer.Sparse Key := [(key1934, -12), (key1935, 12), (key1954, 12), (key1955, -12)]

def row17501 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17502 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17503 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

def row17504 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17505 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17506 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17507 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17508 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17509 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

def row17510 : Integer.Sparse Key := [(key688, 12), (key689, -24), (key691, 12)]

def row17511 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17512 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17513 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

def row17514 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17515 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17516 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17517 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17518 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17519 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

def row17520 : Integer.Sparse Key := [(key1938, -12), (key1939, 12), (key1941, 12), (key1942, -12)]

def row17521 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17522 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17523 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

def row17524 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17525 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17526 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17527 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17528 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17529 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

def row17530 : Integer.Sparse Key := [(key517, -12), (key524, 12), (key549, 12), (key555, -12)]

def row17531 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17532 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17533 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

def row17534 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17535 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17536 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17537 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17538 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17539 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

def row17540 : Integer.Sparse Key := [(key1854, 12), (key1856, -12), (key1887, -12), (key1890, 12)]

def row17541 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17542 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17543 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

def row17544 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17545 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17546 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17547 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17548 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17549 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

def row17550 : Integer.Sparse Key := [(key1866, 12), (key1871, -12), (key1881, -12), (key1889, 12)]

def row17551 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17552 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17553 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

def row17554 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17555 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17556 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17557 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17558 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17559 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

def row17560 : Integer.Sparse Key := [(key1868, -12), (key1871, 12), (key1878, 12), (key1881, -12)]

def row17561 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17562 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17563 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

def row17564 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17565 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17566 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17567 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17568 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17569 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

def row17570 : Integer.Sparse Key := [(key1941, -12), (key1942, 12), (key1950, 12), (key1951, -12)]

def row17571 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17572 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17573 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

def row17574 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17575 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17576 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17577 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17578 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17579 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

def row17580 : Integer.Sparse Key := [(key1863, 12), (key1865, -12), (key1870, -12), (key1872, 12)]

def row17581 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17582 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17583 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

def row17584 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17585 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17586 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17587 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17588 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17589 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

def row17590 : Integer.Sparse Key := [(key536, 12), (key544, -24), (key556, 12)]

def row17591 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17592 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17593 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

def row17594 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17595 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17596 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17597 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17598 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17599 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

def row17600 : Integer.Sparse Key := [(key633, -12), (key635, 12), (key638, 12), (key644, -12)]

def row17601 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17602 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17603 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

def row17604 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17605 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17606 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17607 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17608 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17609 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

def row17610 : Integer.Sparse Key := [(key291, 12), (key294, -24), (key298, 12)]

def row17611 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17612 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17613 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

def row17614 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17615 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17616 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17617 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17618 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17619 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17620 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17621 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17622 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17623 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17624 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17625 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

def row17626 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17627 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17628 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

def row17629 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17630 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17631 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

def row17632 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17633 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17634 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17635 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17636 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17637 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

def row17638 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17639 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17640 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17641 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17642 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17643 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

def row17644 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

def row17645 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

def row17646 : Integer.Sparse Key := [(key72, 4), (key125, -4), (key127, 6), (key135, -8), (key180, 4), (key704, 4), (key709, -8), (key863, 6), (key885, -4)]

def row17647 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17648 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17649 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

def row17650 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17651 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17652 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17653 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17654 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17655 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17656 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17657 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17658 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17659 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17660 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17661 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

def row17662 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

def row17663 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17664 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

def row17665 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17666 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17667 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

def row17668 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17669 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17670 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17671 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17672 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17673 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17674 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17675 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17676 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17677 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17678 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17679 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

def row17680 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17681 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17682 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

def row17683 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17684 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17685 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

def row17686 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17687 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17688 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17689 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17690 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17691 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17692 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17693 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17694 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17695 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17696 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17697 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

def row17698 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17699 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17700 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

def row17701 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17702 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17703 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

def row17704 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17705 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17706 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17707 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17708 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17709 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17710 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17711 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17712 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17713 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17714 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17715 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

def row17716 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

def row17717 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

def row17718 : Integer.Sparse Key := [(key78, 4), (key191, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8)]

def row17719 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17720 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17721 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

def row17722 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17723 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17724 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17725 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17726 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17727 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17728 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17729 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17730 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17731 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17732 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17733 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

def row17734 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17735 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17736 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

def row17737 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17738 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17739 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

def row17740 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17741 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17742 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17743 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17744 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17745 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17746 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17747 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17748 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17749 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17750 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17751 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

def row17752 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17753 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17754 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

def row17755 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17756 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17757 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

def row17758 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17759 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17760 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17761 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17762 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17763 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17764 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17765 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17766 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17767 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17768 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17769 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

def row17770 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17771 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17772 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

def row17773 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17774 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17775 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

def row17776 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17777 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17778 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17779 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17780 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17781 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17782 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17783 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17784 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17785 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17786 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17787 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

def row17788 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17789 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17790 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

def row17791 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17792 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

def row17793 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

def row17794 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17795 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17796 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17797 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17798 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17799 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17800 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17801 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17802 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17803 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17804 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17805 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

def row17806 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17807 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17808 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

def row17809 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17810 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17811 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

def row17812 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17813 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17814 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17815 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17816 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17817 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17818 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17819 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17820 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17821 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17822 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17823 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

def row17824 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17825 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17826 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

def row17827 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17828 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17829 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

def row17830 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17831 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17832 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17833 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17834 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17835 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17836 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17837 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17838 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17839 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17840 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17841 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

def row17842 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17843 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17844 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

def row17845 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17846 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17847 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

def row17848 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17849 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17850 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17851 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17852 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17853 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17854 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17855 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17856 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17857 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17858 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17859 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

def row17860 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17861 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17862 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

def row17863 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17864 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17865 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

def row17866 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17867 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17868 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17869 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17870 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17871 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17872 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17873 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17874 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17875 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17876 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17877 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row17878 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17879 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17880 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

def row17881 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17882 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17883 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

def row17884 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17885 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17886 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17887 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17888 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17889 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17890 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17891 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17892 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17893 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17894 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17895 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row17896 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17897 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17898 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

def row17899 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17900 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17901 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

def row17902 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17903 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17904 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17905 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17906 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17907 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17908 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17909 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17910 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17911 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17912 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17913 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

def row17914 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17915 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17916 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

def row17917 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

def row17918 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

def row17919 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row17920 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17921 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17922 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17923 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17924 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17925 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17926 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17927 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17928 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17929 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17930 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17931 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

def row17932 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17933 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17934 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

def row17935 : Integer.Sparse Key := [(key763, -4), (key765, -2), (key775, -2), (key785, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17936 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, -2), (key773, -2), (key775, -2), (key785, -2), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17937 : Integer.Sparse Key := [(key765, -4), (key767, -4), (key773, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

def row17938 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

def row17939 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

def row17940 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17941 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17942 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17943 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

def row17944 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key810, -4), (key838, -4), (key851, 4)]

def row17945 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key810, -4), (key838, -4), (key851, 4)]

def row17946 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17947 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17948 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17949 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

def row17950 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17951 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17952 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

def row17953 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17954 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17955 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

def row17956 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17957 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17958 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17959 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17960 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17961 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17962 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17963 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17964 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17965 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17966 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17967 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

def row17968 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17969 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17970 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

def row17971 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17972 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17973 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

def row17974 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17975 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17976 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17977 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17978 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17979 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17980 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17981 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17982 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17983 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17984 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17985 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

def row17986 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17987 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17988 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

def row17989 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17990 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17991 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17992 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17993 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17994 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

def row17995 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17996 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17997 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17998 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row17999 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18000 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18001 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18002 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18003 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18004 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

def row18005 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18006 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18007 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

def row18008 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

def row18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18010 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18011 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18012 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18013 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18014 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

def row18015 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18016 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18017 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18018 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18019 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18020 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18021 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18022 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18023 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18024 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

def row18025 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18026 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18027 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

def row18028 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18189 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18190 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18191 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18192 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18193 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18194 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

def row18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

def row18196 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

def row18197 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3110, 2)]

def row18198 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

def row18199 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

def row18200 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2813, 2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3096, -2), (key3106, 2)]

def row18201 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

def row18202 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

def row18203 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2710, -2), (key2715, 2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3066, -2), (key3072, 2), (key3110, 2)]

def row18204 : Integer.Sparse Key := [(key2679, -3), (key2689, 12), (key2710, 6), (key2715, -6), (key2742, -6), (key3047, -3), (key3050, -6), (key3066, 6)]

def row18205 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

def row18206 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

def row18207 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key2813, 2), (key3061, -2), (key3096, -2)]

def row18208 : Integer.Sparse Key := [(key2679, -3), (key2682, -6), (key2689, 12), (key2710, 6), (key2715, -6), (key2740, 6), (key2742, -6), (key3047, -3)]

def row18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18210 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18211 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18212 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18213 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18214 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

def row18215 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18216 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18217 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18218 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18219 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18220 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18221 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18222 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18223 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18224 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

def row18225 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18226 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18227 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

def row18228 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

def row18229 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18230 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18231 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18232 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18233 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18234 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

def row18235 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18236 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18237 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18238 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18239 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18240 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18241 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18242 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18243 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18244 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

def row18245 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18246 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18247 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

def row18248 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

def row18249 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18250 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18251 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18252 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18253 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18254 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

def row18255 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18256 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18257 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18258 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18259 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18260 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18261 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18262 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18263 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18264 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

def row18265 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18266 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18267 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

def row18268 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

def row18269 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18270 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18271 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18272 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18273 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18274 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

def row18275 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18276 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18277 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18278 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18279 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18280 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18281 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18282 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18283 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18284 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

def row18285 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18286 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18287 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

def row18288 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

def row18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18290 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18291 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18292 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

def row18293 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18309 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

end MUB6.Certificate.GramRows

end OAI
end


