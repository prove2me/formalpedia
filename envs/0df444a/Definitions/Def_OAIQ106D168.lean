-- Prove2me | Definitions.Def_OAIQ106D168
-- name    : OAIQ106D168
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:40:28.694516+00:00
-- url     : https://prove2.me/theorems/3385a2de-dc6d-4d91-8c22-84771c807cb9
-- title:
--   Definitions bundle OAIQ106D168 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 562 declarations of OpenAI's Lean: 562 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow19724`, `OAI.MUB6.Certificate.GramRows.rawRow19725`, `OAI.MUB6.Certificate.GramRows.rawRow19726`, `OAI.MUB6.Certificate.GramRows.rawRow19727`, `OAI.MUB6.Certificate.GramRows.rawRow19728`, `OAI.MUB6.Certificate.GramRows.rawRow19729`, `OAI.MUB6.Certificate.GramRows.rawRow1973`, `OAI.MUB6.Certificate.GramRows.rawRow19730`, `OAI.MUB6.Certificate.GramRows.rawRow19731`, `OAI.MUB6.Certificate.GramRows.rawRow19732`, `OAI.MUB6.Certificate.GramRows.rawRow19733`, `OAI.MUB6.Certificate.GramRows.rawRow19734`, `OAI.MUB6.Certificate.GramRows.rawRow19735`, `OAI.MUB6.Certificate.GramRows.rawRow19736`, `OAI.MUB6.Certificate.GramRows.rawRow19737`, `OAI.MUB6.Certificate.GramRows.rawRow19738`, `OAI.MUB6.Certificate.GramRows.rawRow19739`, `OAI.MUB6.Certificate.GramRows.rawRow1974`, `OAI.MUB6.Certificate.GramRows.rawRow19740`, `OAI.MUB6.Certificate.GramRows.rawRow19741`, `OAI.MUB6.Certificate.GramRows.rawRow19742`, `OAI.MUB6.Certificate.GramRows.rawRow19743`, `OAI.MUB6.Certificate.GramRows.rawRow19744`, `OAI.MUB6.Certificate.GramRows.rawRow19745`, `OAI.MUB6.Certificate.GramRows.rawRow19746`, `OAI.MUB6.Certificate.GramRows.rawRow19747`, `OAI.MUB6.Certificate.GramRows.rawRow19748`, `OAI.MUB6.Certificate.GramRows.rawRow19749`, `OAI.MUB6.Certificate.GramRows.rawRow1975`, `OAI.MUB6.Certificate.GramRows.rawRow19750`, `OAI.MUB6.Certificate.GramRows.rawRow19751`, `OAI.MUB6.Certificate.GramRows.rawRow19752`, `OAI.MUB6.Certificate.GramRows.rawRow19753`, `OAI.MUB6.Certificate.GramRows.rawRow19754`, `OAI.MUB6.Certificate.GramRows.rawRow19755`, `OAI.MUB6.Certificate.GramRows.rawRow19756`, `OAI.MUB6.Certificate.GramRows.rawRow19757`, `OAI.MUB6.Certificate.GramRows.rawRow19758`, `OAI.MUB6.Certificate.GramRows.rawRow19759`, `OAI.MUB6.Certificate.GramRows.rawRow1976` and 522 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block178`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block178.lean), [`MutuallyUnbiased_GramRows_Block179`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block179.lean), [`MutuallyUnbiased_GramRows_Block180`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block180.lean), [`MutuallyUnbiased_GramRows_Block181`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block181.lean), [`MutuallyUnbiased_GramRows_Block182`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block182.lean), [`MutuallyUnbiased_GramRows_Block39`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block39.lean), [`MutuallyUnbiased_TaoCertificate_Merge20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge20.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D094
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20 : Integer.Sparse Key := [(key385, -1), (key388, -1), (key397, 2), (key406, 1), (key409, 1), (key442, -1), (key469, -1), (key418, -2), (key450, 1), (key475, 1), (key248, 1), (key251, 1), (key260, -2), (key316, -1), (key319, -1), (key442, 1), (key595, 1), (key328, 2), (key450, -1), (key601, -1), (key236, -1), (key239, -1), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key335, -1), (key340, -1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key239, 2), (key251, -1), (key260, -1), (key305, -2), (key319, 1), (key328, 1), (key388, 1), (key397, 1), (key409, -1), (key418, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 2), (key1299, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1394, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2)]

def rawRow19725 : Integer.Sparse Key := [(key1299, 2), (key1291, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2)]

def rawRow19726 : Integer.Sparse Key := [(key1299, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2)]

def rawRow19727 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2)]

def rawRow19728 : Integer.Sparse Key := [(key1319, 2), (key1311, 2), (key1352, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2)]

def rawRow19729 : Integer.Sparse Key := [(key1311, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2)]

def rawRow19730 : Integer.Sparse Key := [(key1352, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2)]

def rawRow19731 : Integer.Sparse Key := [(key1319, 2), (key1352, 2), (key1311, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2)]

def rawRow19732 : Integer.Sparse Key := [(key1352, 2), (key1319, 2), (key1311, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2)]

def rawRow19733 : Integer.Sparse Key := [(key1327, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2)]

def rawRow19734 : Integer.Sparse Key := [(key1327, 2), (key1355, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2)]

def rawRow19735 : Integer.Sparse Key := [(key1355, 2), (key1327, 2), (key1327, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1445, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2)]

def rawRow19736 : Integer.Sparse Key := [(key1386, 2), (key1394, 2), (key1394, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2)]

def rawRow19737 : Integer.Sparse Key := [(key1394, 2), (key1386, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2)]

def rawRow19738 : Integer.Sparse Key := [(key1394, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2)]

def rawRow19739 : Integer.Sparse Key := [(key1541, 2), (key1549, 2), (key1897, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2)]

def rawRow19740 : Integer.Sparse Key := [(key1549, 2), (key1541, 2), (key1897, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2)]

def rawRow19741 : Integer.Sparse Key := [(key1541, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2)]

def rawRow19742 : Integer.Sparse Key := [(key1897, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2)]

def rawRow19743 : Integer.Sparse Key := [(key1549, 2), (key1897, 2), (key1541, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2)]

def rawRow19744 : Integer.Sparse Key := [(key1897, 2), (key1549, 2), (key1541, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2)]

def rawRow19745 : Integer.Sparse Key := [(key1557, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2)]

def rawRow19746 : Integer.Sparse Key := [(key1557, 2), (key1900, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2)]

def rawRow19747 : Integer.Sparse Key := [(key1900, 2), (key1557, 2), (key1557, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2)]

def rawRow19748 : Integer.Sparse Key := [(key1419, 2), (key1427, 2), (key1473, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2)]

def rawRow19749 : Integer.Sparse Key := [(key1427, 2), (key1419, 2), (key1473, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2)]

def rawRow19750 : Integer.Sparse Key := [(key1419, 2), (key1473, 2), (key1427, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2)]

def rawRow19751 : Integer.Sparse Key := [(key1473, 2), (key1419, 2), (key1427, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2)]

def rawRow19752 : Integer.Sparse Key := [(key1427, 2), (key1473, 2), (key1419, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2)]

def rawRow19753 : Integer.Sparse Key := [(key1473, 2), (key1427, 2), (key1419, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2)]

def rawRow19754 : Integer.Sparse Key := [(key1568, 2), (key1576, 2), (key1904, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2)]

def rawRow19755 : Integer.Sparse Key := [(key1576, 2), (key1568, 2), (key1904, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2)]

def rawRow19756 : Integer.Sparse Key := [(key1568, 2), (key1904, 2), (key1576, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2)]

def rawRow19757 : Integer.Sparse Key := [(key1904, 2), (key1568, 2), (key1576, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2)]

def rawRow19758 : Integer.Sparse Key := [(key1576, 2), (key1904, 2), (key1568, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2)]

def rawRow19759 : Integer.Sparse Key := [(key1904, 2), (key1576, 2), (key1568, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2)]

def rawRow19760 : Integer.Sparse Key := [(key1617, 2), (key1682, 2), (key1919, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1291, 2), (key1355, 2), (key1386, 2), (key1481, 2), (key1900, 2), (key1912, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2)]

def rawRow19761 : Integer.Sparse Key := [(key1682, 2), (key1617, 2), (key1919, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1355, 2), (key1291, 2), (key1481, 2), (key1386, 2), (key1912, 2), (key1900, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2)]

def rawRow19762 : Integer.Sparse Key := [(key1617, 2), (key1919, 2), (key1682, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1386, 2), (key1900, 2), (key1291, 2), (key1912, 2), (key1355, 2), (key1481, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2)]

def rawRow19763 : Integer.Sparse Key := [(key1919, 2), (key1617, 2), (key1682, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1900, 2), (key1386, 2), (key1912, 2), (key1291, 2), (key1481, 2), (key1355, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2)]

def rawRow19764 : Integer.Sparse Key := [(key1682, 2), (key1919, 2), (key1617, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1481, 2), (key1912, 2), (key1355, 2), (key1900, 2), (key1291, 2), (key1386, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2)]

def rawRow19765 : Integer.Sparse Key := [(key1919, 2), (key1682, 2), (key1617, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1912, 2), (key1481, 2), (key1900, 2), (key1355, 2), (key1386, 2), (key1291, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2)]

def rawRow19766 : Integer.Sparse Key := [(key1625, 2), (key1684, 2), (key1921, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2)]

def rawRow19767 : Integer.Sparse Key := [(key1684, 2), (key1625, 2), (key1921, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2)]

def rawRow19768 : Integer.Sparse Key := [(key1625, 2), (key1921, 2), (key1684, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2)]

def rawRow19769 : Integer.Sparse Key := [(key1921, 2), (key1625, 2), (key1684, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2)]

def rawRow19770 : Integer.Sparse Key := [(key1684, 2), (key1921, 2), (key1625, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2)]

def rawRow19771 : Integer.Sparse Key := [(key1921, 2), (key1684, 2), (key1625, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2)]

def rawRow19772 : Integer.Sparse Key := [(key1445, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2)]

def rawRow19773 : Integer.Sparse Key := [(key1445, 2), (key1481, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2)]

def rawRow19774 : Integer.Sparse Key := [(key1481, 2), (key1445, 2), (key1445, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1327, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2)]

def rawRow19775 : Integer.Sparse Key := [(key1594, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2)]

def rawRow19776 : Integer.Sparse Key := [(key1594, 2), (key1912, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2)]

def rawRow19777 : Integer.Sparse Key := [(key1912, 2), (key1594, 2), (key1594, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2)]

def rawRow19778 : Integer.Sparse Key := [(key1634, 2), (key1690, 2), (key1927, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2)]

def rawRow19779 : Integer.Sparse Key := [(key1690, 2), (key1634, 2), (key1927, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2)]

def rawRow19780 : Integer.Sparse Key := [(key1634, 2), (key1927, 2), (key1690, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2)]

def rawRow19781 : Integer.Sparse Key := [(key1927, 2), (key1634, 2), (key1690, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2)]

def rawRow19782 : Integer.Sparse Key := [(key1690, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2)]

def rawRow19783 : Integer.Sparse Key := [(key1927, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2)]

def rawRow19785 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

def rawRow19786 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

def rawRow19787 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

def rawRow19788 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

def rawRow19789 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

def rawRow19790 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

def rawRow19791 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

def rawRow19792 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

def rawRow19793 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

def rawRow19794 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

def rawRow19795 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

def rawRow19796 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

def rawRow19797 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

def rawRow19798 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

def rawRow19799 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

def rawRow19800 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

def rawRow19801 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

def rawRow19802 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

def rawRow19803 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

def rawRow19804 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

def rawRow19805 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

def rawRow19806 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

def rawRow19807 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

def rawRow19808 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

def rawRow19809 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

def rawRow19810 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

def rawRow19811 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

def rawRow19812 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

def rawRow19813 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

def rawRow19814 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

def rawRow19815 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

def rawRow19816 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

def rawRow19817 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

def rawRow19818 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

def rawRow19819 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

def rawRow19820 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24)]

def rawRow19821 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24)]

def rawRow19822 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24)]

def rawRow19823 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24)]

def rawRow19824 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24)]

def rawRow19825 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24)]

def rawRow19826 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

def rawRow19827 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

def rawRow19828 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

def rawRow19829 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

def rawRow19830 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

def rawRow19831 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

def rawRow19832 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

def rawRow19833 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

def rawRow19834 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

def rawRow19835 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

def rawRow19836 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

def rawRow19837 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

def rawRow19838 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

def rawRow19839 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19840 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

def rawRow19841 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

def rawRow19842 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

def rawRow19843 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

def rawRow19844 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key381, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key486, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key659, 6), (key663, 6)]

def rawRow19845 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key23, 6), (key35, 6), (key381, 6), (key375, 6), (key381, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key486, 6), (key490, 6), (key486, 6), (key654, 6), (key659, 6), (key663, 6), (key659, 6)]

def rawRow19846 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key381, 6), (key375, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key490, 6), (key486, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key659, 6)]

def rawRow19847 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key23, 6), (key426, 6), (key432, 6), (key486, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key381, 6), (key432, 6), (key460, 6), (key659, 6), (key654, 6), (key659, 6), (key663, 6)]

def rawRow19848 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key35, 6), (key23, 6), (key432, 6), (key426, 6), (key486, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key381, 6), (key460, 6), (key432, 6), (key659, 6), (key654, 6), (key663, 6), (key659, 6)]

def rawRow19849 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key23, 6), (key23, 6), (key426, 6), (key486, 6), (key432, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key432, 6), (key381, 6), (key460, 6), (key659, 6), (key659, 6), (key654, 6), (key663, 6)]

def rawRow19850 : Integer.Sparse Key := [(key35, 6), (key18, 6), (key23, 6), (key23, 6), (key486, 6), (key426, 6), (key432, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key432, 6), (key460, 6), (key381, 6), (key659, 6), (key659, 6), (key663, 6), (key654, 6)]

def rawRow19851 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key18, 6), (key23, 6), (key432, 6), (key486, 6), (key426, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key460, 6), (key381, 6), (key432, 6), (key659, 6), (key663, 6), (key654, 6), (key659, 6)]

def rawRow19852 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key18, 6), (key23, 6), (key486, 6), (key432, 6), (key426, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key460, 6), (key432, 6), (key381, 6), (key659, 6), (key663, 6), (key659, 6), (key654, 6)]

def rawRow19853 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key460, 6), (key490, 6), (key381, 6), (key381, 6), (key432, 6), (key432, 6), (key486, 6), (key486, 6), (key375, 6), (key426, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key659, 6)]

def rawRow19854 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key23, 6), (key18, 6), (key460, 6), (key490, 6), (key460, 6), (key432, 6), (key486, 6), (key381, 6), (key486, 6), (key381, 6), (key432, 6), (key426, 6), (key375, 6), (key426, 6), (key663, 6), (key659, 6), (key654, 6), (key659, 6)]

def rawRow19855 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key460, 6), (key486, 6), (key432, 6), (key486, 6), (key381, 6), (key432, 6), (key381, 6), (key426, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key659, 6), (key654, 6)]

def rawRow19856 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key212, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key659, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key486, 6), (key490, 6)]

def rawRow19857 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key48, 6), (key74, 6), (key212, 6), (key206, 6), (key212, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key659, 6), (key663, 6), (key659, 6), (key218, 6), (key486, 6), (key490, 6), (key486, 6)]

def rawRow19858 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key212, 6), (key206, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key663, 6), (key659, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key486, 6)]

def rawRow19859 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key48, 6), (key426, 6), (key432, 6), (key659, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key212, 6), (key432, 6), (key460, 6), (key486, 6), (key218, 6), (key486, 6), (key490, 6)]

def rawRow19860 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key74, 6), (key48, 6), (key432, 6), (key426, 6), (key659, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key212, 6), (key460, 6), (key432, 6), (key486, 6), (key218, 6), (key490, 6), (key486, 6)]

def rawRow19861 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key48, 6), (key48, 6), (key426, 6), (key659, 6), (key432, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key432, 6), (key212, 6), (key460, 6), (key486, 6), (key486, 6), (key218, 6), (key490, 6)]

def rawRow19862 : Integer.Sparse Key := [(key74, 6), (key43, 6), (key48, 6), (key48, 6), (key659, 6), (key426, 6), (key432, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key432, 6), (key460, 6), (key212, 6), (key486, 6), (key486, 6), (key490, 6), (key218, 6)]

def rawRow19863 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key43, 6), (key48, 6), (key432, 6), (key659, 6), (key426, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key460, 6), (key212, 6), (key432, 6), (key486, 6), (key490, 6), (key218, 6), (key486, 6)]

def rawRow19864 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key43, 6), (key48, 6), (key659, 6), (key432, 6), (key426, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key460, 6), (key432, 6), (key212, 6), (key486, 6), (key490, 6), (key486, 6), (key218, 6)]

def rawRow19865 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key460, 6), (key663, 6), (key212, 6), (key212, 6), (key432, 6), (key432, 6), (key659, 6), (key659, 6), (key206, 6), (key426, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key486, 6)]

def rawRow19866 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key48, 6), (key43, 6), (key460, 6), (key663, 6), (key460, 6), (key432, 6), (key659, 6), (key212, 6), (key659, 6), (key212, 6), (key432, 6), (key426, 6), (key206, 6), (key426, 6), (key490, 6), (key486, 6), (key218, 6), (key486, 6)]

def rawRow19867 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key460, 6), (key659, 6), (key432, 6), (key659, 6), (key212, 6), (key432, 6), (key212, 6), (key426, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key486, 6), (key218, 6)]

def rawRow19868 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key115, 6), (key137, 6), (key18, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

def rawRow19869 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key115, 6), (key137, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6)]

def rawRow19870 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key105, 6), (key137, 6), (key18, 6), (key35, 6), (key23, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key659, 6), (key654, 6), (key663, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6)]

def rawRow19871 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key105, 6), (key137, 6), (key35, 6), (key18, 6), (key23, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key659, 6), (key663, 6), (key654, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6)]

def rawRow19872 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key100, 6), (key137, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6)]

def rawRow19873 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key100, 6), (key137, 6), (key35, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key654, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6)]

def rawRow19874 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key137, 6), (key115, 6), (key43, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key490, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6)]

def rawRow19875 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key137, 6), (key115, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6)]

def rawRow19876 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key105, 6), (key115, 6), (key43, 6), (key74, 6), (key48, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key486, 6), (key218, 6), (key490, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6)]

def rawRow19877 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key105, 6), (key115, 6), (key74, 6), (key43, 6), (key48, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key486, 6), (key490, 6), (key218, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6)]

def rawRow19878 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key100, 6), (key115, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6)]

def rawRow19879 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key100, 6), (key115, 6), (key74, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key218, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6)]

def rawRow19880 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key137, 6), (key105, 6), (key100, 6), (key115, 6), (key137, 6), (key18, 6), (key35, 6), (key375, 6), (key490, 6), (key654, 6), (key663, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6), (key460, 6)]

def rawRow19881 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key137, 6), (key105, 6), (key115, 6), (key100, 6), (key137, 6), (key35, 6), (key18, 6), (key490, 6), (key375, 6), (key663, 6), (key654, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6), (key381, 6)]

def rawRow19882 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key115, 6), (key105, 6), (key100, 6), (key137, 6), (key115, 6), (key43, 6), (key74, 6), (key206, 6), (key663, 6), (key218, 6), (key490, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6), (key460, 6)]

def rawRow19883 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key115, 6), (key105, 6), (key137, 6), (key100, 6), (key115, 6), (key74, 6), (key43, 6), (key663, 6), (key206, 6), (key490, 6), (key218, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6), (key212, 6)]

def rawRow19884 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key100, 6), (key196, 6), (key200, 6), (key35, 6), (key74, 6), (key18, 6), (key375, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6), (key381, 6)]

def rawRow19885 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key100, 6), (key105, 6), (key137, 6), (key115, 6), (key100, 6), (key200, 6), (key196, 6), (key74, 6), (key35, 6), (key43, 6), (key206, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6), (key212, 6)]

def rawRow19886 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key137, 6), (key100, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6)]

def rawRow19887 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key137, 6), (key100, 6), (key196, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key375, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6)]

def rawRow19888 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key115, 6), (key100, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6)]

def rawRow19889 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key115, 6), (key100, 6), (key200, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key206, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6)]

def rawRow19890 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key105, 6), (key100, 6), (key196, 6), (key200, 6), (key195, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key100, 6), (key18, 6), (key375, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6)]

def rawRow19891 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key105, 6), (key100, 6), (key200, 6), (key196, 6), (key195, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key100, 6), (key43, 6), (key206, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6)]

def rawRow19892 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key23, 6), (key35, 6), (key48, 6), (key48, 6), (key105, 6), (key105, 6), (key115, 6), (key115, 6), (key74, 6), (key137, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key426, 6)]

def rawRow19893 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key195, 6), (key200, 6), (key23, 6), (key35, 6), (key23, 6), (key105, 6), (key115, 6), (key48, 6), (key115, 6), (key48, 6), (key105, 6), (key137, 6), (key74, 6), (key137, 6), (key18, 6), (key426, 6), (key375, 6), (key426, 6)]

def rawRow19894 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key23, 6), (key115, 6), (key105, 6), (key115, 6), (key48, 6), (key105, 6), (key48, 6), (key137, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key426, 6), (key375, 6)]

def rawRow19895 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key48, 6), (key74, 6), (key23, 6), (key23, 6), (key105, 6), (key105, 6), (key137, 6), (key137, 6), (key35, 6), (key115, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key426, 6)]

def rawRow19896 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key195, 6), (key196, 6), (key48, 6), (key74, 6), (key48, 6), (key105, 6), (key137, 6), (key23, 6), (key137, 6), (key23, 6), (key105, 6), (key115, 6), (key35, 6), (key115, 6), (key43, 6), (key426, 6), (key206, 6), (key426, 6)]

def rawRow19897 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key48, 6), (key137, 6), (key105, 6), (key137, 6), (key23, 6), (key105, 6), (key23, 6), (key115, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key426, 6), (key206, 6)]

def rawRow19898 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key200, 6), (key195, 6), (key105, 6), (key115, 6), (key137, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key23, 6), (key48, 6), (key105, 6), (key100, 6), (key18, 6), (key375, 6), (key426, 6)]

def rawRow19899 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key200, 6), (key195, 6), (key115, 6), (key105, 6), (key137, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key23, 6), (key105, 6), (key48, 6), (key100, 6), (key18, 6), (key426, 6), (key375, 6)]

def rawRow19900 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key196, 6), (key195, 6), (key105, 6), (key137, 6), (key115, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key48, 6), (key23, 6), (key105, 6), (key100, 6), (key43, 6), (key206, 6), (key426, 6)]

def rawRow19901 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key196, 6), (key195, 6), (key137, 6), (key105, 6), (key115, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key48, 6), (key105, 6), (key23, 6), (key100, 6), (key43, 6), (key426, 6), (key206, 6)]

def rawRow19902 : Integer.Sparse Key := [(key196, 6), (key200, 6), (key195, 6), (key195, 6), (key115, 6), (key137, 6), (key105, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key105, 6), (key23, 6), (key48, 6), (key100, 6), (key100, 6), (key18, 6), (key375, 6)]

def rawRow19903 : Integer.Sparse Key := [(key200, 6), (key196, 6), (key195, 6), (key195, 6), (key137, 6), (key115, 6), (key105, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key105, 6), (key48, 6), (key23, 6), (key100, 6), (key100, 6), (key43, 6), (key206, 6)]

def rawRow19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1830, 6)]

def rawRow19965 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1807, 6)]

def rawRow19966 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1807, 6)]

def rawRow19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1830, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19968 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1807, 6)]

def rawRow19969 : Integer.Sparse Key := [(key1252, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1830, 6)]

def rawRow19970 : Integer.Sparse Key := [(key1266, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1766, 6)]

def rawRow19971 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1807, 6)]

def rawRow19972 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1766, 6)]

def rawRow19973 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1807, 6)]

def rawRow19974 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1807, 6)]

def rawRow19975 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1766, 6)]

def rawRow19976 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1672, 6)]

def rawRow19977 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1649, 6)]

def rawRow19978 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1649, 6)]

def rawRow19979 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1672, 6)]

def rawRow19980 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1649, 6)]

def rawRow19981 : Integer.Sparse Key := [(key1527, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1672, 6)]

def rawRow19982 : Integer.Sparse Key := [(key1766, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1266, 6)]

def rawRow19983 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1649, 6)]

def rawRow19984 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1266, 6)]

def rawRow19985 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1649, 6)]

def rawRow19986 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1649, 6)]

def rawRow19987 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1266, 6)]

def rawRow19988 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6)]

def rawRow19989 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6)]

def rawRow19990 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6)]

def rawRow19991 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6)]

def rawRow19992 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6)]

def rawRow19993 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6)]

def rawRow19994 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6)]

def rawRow19995 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6)]

def rawRow19996 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6)]

def rawRow19997 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6)]

def rawRow19998 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6)]

def rawRow19999 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6)]

def rawRow20000 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1527, 6), (key1672, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1638, 6)]

def rawRow20001 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1672, 6), (key1527, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1532, 6)]

def rawRow20002 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1252, 6), (key1830, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1638, 6)]

def rawRow20003 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1830, 6), (key1252, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1257, 6)]

def rawRow20004 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1266, 6), (key1766, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1532, 6)]

def rawRow20005 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1766, 6), (key1266, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1257, 6)]

def rawRow20006 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6)]

def rawRow20007 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6)]

def rawRow20008 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6)]

def rawRow20009 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6)]

def rawRow20010 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6)]

def rawRow20011 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6)]

def rawRow20012 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1605, 6)]

def rawRow20013 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1605, 6)]

def rawRow20014 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1527, 6)]

def rawRow20015 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1605, 6)]

def rawRow20016 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1605, 6)]

def rawRow20017 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1252, 6)]

def rawRow20018 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1605, 6)]

def rawRow20019 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1527, 6)]

def rawRow20020 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1605, 6)]

def rawRow20021 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1252, 6)]

def rawRow20022 : Integer.Sparse Key := [(key1672, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1527, 6)]

def rawRow20023 : Integer.Sparse Key := [(key1830, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1252, 6)]

def rawRow20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

def rawRow20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

def rawRow20026 : Integer.Sparse Key := [(key1293, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

def rawRow20027 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

def rawRow20028 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

def rawRow20029 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

def rawRow20030 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

def rawRow20031 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

def rawRow20032 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

def rawRow20033 : Integer.Sparse Key := [(key1323, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

def rawRow20034 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

def rawRow20035 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

def rawRow20036 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

def rawRow20037 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

def rawRow20038 : Integer.Sparse Key := [(key1388, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

def rawRow20039 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

def rawRow20040 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

def rawRow20041 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

def rawRow20042 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

def rawRow20043 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

def rawRow20044 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

def rawRow20045 : Integer.Sparse Key := [(key1553, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

def rawRow20046 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

def rawRow20047 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

def rawRow20048 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

def rawRow20049 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

def rawRow20050 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

def rawRow20051 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

def rawRow20052 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

def rawRow20053 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

def rawRow20054 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

def rawRow20055 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

def rawRow20056 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

def rawRow20057 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

def rawRow20058 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

def rawRow20059 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

def rawRow20060 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1293, 6), (key1323, 6), (key1388, 6), (key1441, 6), (key1553, 6), (key1590, 6)]

def rawRow20061 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1323, 6), (key1293, 6), (key1441, 6), (key1388, 6), (key1590, 6), (key1553, 6)]

def rawRow20062 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1388, 6), (key1553, 6), (key1293, 6), (key1590, 6), (key1323, 6), (key1441, 6)]

def rawRow20063 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1553, 6), (key1388, 6), (key1590, 6), (key1293, 6), (key1441, 6), (key1323, 6)]

def rawRow20064 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1441, 6), (key1590, 6), (key1323, 6), (key1553, 6), (key1293, 6), (key1388, 6)]

def rawRow20065 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1590, 6), (key1441, 6), (key1553, 6), (key1323, 6), (key1388, 6), (key1293, 6)]

def rawRow20066 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

def rawRow20067 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

def rawRow20068 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

def rawRow20069 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

def rawRow20070 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

def rawRow20071 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

def rawRow20072 : Integer.Sparse Key := [(key1441, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

def rawRow20073 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

def rawRow20074 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

def rawRow20075 : Integer.Sparse Key := [(key1590, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

def rawRow20076 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

def rawRow20077 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

def rawRow20078 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

def rawRow20079 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

def rawRow20080 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

def rawRow20081 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

def rawRow20082 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

def rawRow20083 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

def rawRow20084 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key627, 24), (key629, 24), (key640, 24)]

def rawRow20085 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key629, 24), (key640, 24)]

def rawRow20086 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key629, 24), (key640, 24)]

def rawRow20087 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key627, 24), (key640, 24)]

def rawRow20088 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key627, 24), (key640, 24)]

def rawRow20089 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key627, 24), (key640, 24)]

def rawRow20090 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key627, 24), (key640, 24)]

def rawRow20091 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key627, 24), (key640, 24)]

def rawRow20092 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key627, 24), (key640, 24)]

def rawRow20093 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key626, 24), (key640, 24)]

def rawRow20094 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key626, 24), (key640, 24)]

def rawRow20095 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key626, 24), (key640, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20098 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key640, 24), (key629, 24)]

def rawRow20099 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key627, 24), (key629, 24)]

def rawRow20100 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key627, 24), (key629, 24)]

def rawRow20101 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key627, 24), (key629, 24)]

def rawRow20102 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key627, 24), (key629, 24)]

def rawRow20103 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key627, 24), (key629, 24)]

def rawRow20104 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key627, 24), (key629, 24)]

def rawRow20105 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key626, 24), (key629, 24)]

def rawRow20106 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key626, 24), (key629, 24)]

def rawRow20107 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key626, 24), (key629, 24)]

def rawRow20108 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key640, 24), (key627, 24)]

def rawRow20109 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key640, 24), (key627, 24)]

def rawRow20110 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key640, 24), (key627, 24)]

def rawRow20111 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key640, 24), (key627, 24)]

def rawRow20112 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key640, 24), (key627, 24)]

def rawRow20113 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key640, 24), (key627, 24)]

def rawRow20114 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key629, 24), (key627, 24)]

def rawRow20115 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key629, 24), (key627, 24)]

def rawRow20116 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key629, 24), (key627, 24)]

def rawRow20117 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key629, 24), (key627, 24)]

def rawRow20118 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key629, 24), (key627, 24)]

def rawRow20119 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key629, 24), (key627, 24)]

def rawRow20120 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key640, 24), (key627, 24), (key627, 24)]

def rawRow20121 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key640, 24), (key627, 24), (key627, 24)]

def rawRow20122 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key629, 24), (key627, 24), (key627, 24)]

def rawRow20123 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key629, 24), (key627, 24), (key627, 24)]

def rawRow20124 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key626, 24), (key627, 24), (key627, 24)]

def rawRow20125 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key626, 24), (key627, 24), (key627, 24)]

def rawRow20126 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key626, 24), (key627, 24)]

def rawRow20127 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key626, 24), (key627, 24)]

def rawRow20128 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key626, 24), (key627, 24)]

def rawRow20129 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key626, 24), (key627, 24)]

def rawRow20130 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key626, 24), (key627, 24)]

def rawRow20131 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key626, 24), (key627, 24)]

def rawRow20132 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key640, 24), (key626, 24)]

def rawRow20133 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key640, 24), (key626, 24)]

def rawRow20134 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key640, 24), (key626, 24)]

def rawRow20135 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key629, 24), (key626, 24)]

def rawRow20136 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key629, 24), (key626, 24)]

def rawRow20137 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key629, 24), (key626, 24)]

def rawRow20138 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key627, 24), (key626, 24)]

def rawRow20139 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key627, 24), (key626, 24)]

def rawRow20140 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key627, 24), (key626, 24)]

def rawRow20141 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key627, 24), (key626, 24)]

def rawRow20142 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key627, 24), (key626, 24)]

def rawRow20143 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key627, 24), (key626, 24)]

def rawRow20144 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1628, 12)]

def rawRow20145 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1628, 12)]

def rawRow20146 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1628, 12)]

def rawRow20147 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1585, 12)]

def rawRow20148 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1585, 12)]

def rawRow20149 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1585, 12)]

def rawRow20150 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1585, 12)]

def rawRow20151 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1585, 12)]

def rawRow20152 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1585, 12)]

def rawRow20153 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1584, 12)]

def rawRow20154 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1584, 12)]

def rawRow20155 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1584, 12)]

def rawRow20156 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1628, 12)]

def rawRow20157 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1628, 12)]

def rawRow20158 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1628, 12)]

def rawRow20159 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1436, 12)]

def rawRow20160 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1436, 12)]

def rawRow20161 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1436, 12)]

def rawRow20162 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1436, 12)]

def rawRow20163 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1436, 12)]

def rawRow20164 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1436, 12)]

def rawRow20165 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1435, 12)]

def rawRow20166 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1435, 12)]

def rawRow20167 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1435, 12)]

def rawRow20168 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1585, 12)]

def rawRow20169 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12)]

def rawRow20170 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1585, 12)]

def rawRow20171 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1585, 12)]

def rawRow20172 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12)]

def rawRow20173 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1585, 12)]

def rawRow20174 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1436, 12)]

def rawRow20175 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12)]

def rawRow20176 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1436, 12)]

def rawRow20177 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1436, 12)]

def rawRow20178 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12)]

def rawRow20179 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1436, 12)]

def rawRow20180 : Integer.Sparse Key := [(key1435, 12), (key1584, 12), (key1628, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12)]

def rawRow20181 : Integer.Sparse Key := [(key1435, 12), (key1628, 12), (key1584, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12)]

def rawRow20182 : Integer.Sparse Key := [(key1584, 12), (key1435, 12), (key1628, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12)]

def rawRow20183 : Integer.Sparse Key := [(key1584, 12), (key1628, 12), (key1435, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12)]

def rawRow20184 : Integer.Sparse Key := [(key1628, 12), (key1435, 12), (key1584, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12)]

def rawRow20185 : Integer.Sparse Key := [(key1628, 12), (key1584, 12), (key1435, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12)]

def rawRow20186 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12)]

def rawRow20187 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1407, 12)]

def rawRow20188 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12)]

def rawRow20189 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1407, 12)]

def rawRow20190 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1407, 12)]

def rawRow20191 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1407, 12)]

def rawRow20192 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1584, 12)]

def rawRow20193 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1584, 12)]

def rawRow20194 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1584, 12)]

def rawRow20195 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1435, 12)]

def rawRow20196 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1435, 12)]

def rawRow20197 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1435, 12)]

def rawRow20198 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1407, 12)]

def rawRow20199 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1407, 12)]

def rawRow20200 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1407, 12)]

def rawRow20201 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1407, 12)]

def rawRow20202 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1407, 12)]

def rawRow20203 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1407, 12)]

def rawRow20204 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key352, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key520, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key541, 6), (key677, 6)]

def rawRow20205 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key283, 6), (key292, 6), (key352, 6), (key349, 6), (key352, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key520, 6), (key671, 6), (key520, 6), (key369, 6), (key541, 6), (key677, 6), (key541, 6)]

def rawRow20206 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key352, 6), (key349, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key671, 6), (key520, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key541, 6)]

def rawRow20207 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key292, 6), (key283, 6), (key506, 6), (key509, 6), (key520, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key352, 6), (key509, 6), (key667, 6), (key541, 6), (key369, 6), (key541, 6), (key677, 6)]

def rawRow20208 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key292, 6), (key283, 6), (key509, 6), (key506, 6), (key520, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key352, 6), (key667, 6), (key509, 6), (key541, 6), (key369, 6), (key677, 6), (key541, 6)]

def rawRow20209 : Integer.Sparse Key := [(key280, 6), (key292, 6), (key283, 6), (key283, 6), (key506, 6), (key520, 6), (key509, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key509, 6), (key352, 6), (key667, 6), (key541, 6), (key541, 6), (key369, 6), (key677, 6)]

def rawRow20210 : Integer.Sparse Key := [(key292, 6), (key280, 6), (key283, 6), (key283, 6), (key520, 6), (key506, 6), (key509, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key509, 6), (key667, 6), (key352, 6), (key541, 6), (key541, 6), (key677, 6), (key369, 6)]

def rawRow20211 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key280, 6), (key283, 6), (key509, 6), (key520, 6), (key506, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key667, 6), (key352, 6), (key509, 6), (key541, 6), (key677, 6), (key369, 6), (key541, 6)]

def rawRow20212 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key280, 6), (key283, 6), (key520, 6), (key509, 6), (key506, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key667, 6), (key509, 6), (key352, 6), (key541, 6), (key677, 6), (key541, 6), (key369, 6)]

def rawRow20213 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key667, 6), (key671, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key349, 6), (key506, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key541, 6)]

def rawRow20214 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key283, 6), (key280, 6), (key667, 6), (key671, 6), (key667, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key506, 6), (key349, 6), (key506, 6), (key677, 6), (key541, 6), (key369, 6), (key541, 6)]

def rawRow20215 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key667, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key506, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key541, 6), (key369, 6)]

def rawRow20216 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key283, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key541, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key520, 6), (key671, 6)]

def rawRow20217 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key352, 6), (key369, 6), (key283, 6), (key280, 6), (key283, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key541, 6), (key677, 6), (key541, 6), (key292, 6), (key520, 6), (key671, 6), (key520, 6)]

def rawRow20218 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key283, 6), (key280, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key677, 6), (key541, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key520, 6)]

def rawRow20219 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key369, 6), (key352, 6), (key506, 6), (key509, 6), (key541, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key283, 6), (key509, 6), (key667, 6), (key520, 6), (key292, 6), (key520, 6), (key671, 6)]

def rawRow20220 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key369, 6), (key352, 6), (key509, 6), (key506, 6), (key541, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key283, 6), (key667, 6), (key509, 6), (key520, 6), (key292, 6), (key671, 6), (key520, 6)]

def rawRow20221 : Integer.Sparse Key := [(key349, 6), (key369, 6), (key352, 6), (key352, 6), (key506, 6), (key541, 6), (key509, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key509, 6), (key283, 6), (key667, 6), (key520, 6), (key520, 6), (key292, 6), (key671, 6)]

def rawRow20222 : Integer.Sparse Key := [(key369, 6), (key349, 6), (key352, 6), (key352, 6), (key541, 6), (key506, 6), (key509, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key509, 6), (key667, 6), (key283, 6), (key520, 6), (key520, 6), (key671, 6), (key292, 6)]

def rawRow20223 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key349, 6), (key352, 6), (key509, 6), (key541, 6), (key506, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key667, 6), (key283, 6), (key509, 6), (key520, 6), (key671, 6), (key292, 6), (key520, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20224 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key349, 6), (key352, 6), (key541, 6), (key509, 6), (key506, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key667, 6), (key509, 6), (key283, 6), (key520, 6), (key671, 6), (key520, 6), (key292, 6)]

def rawRow20225 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key667, 6), (key677, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key280, 6), (key506, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key520, 6)]

def rawRow20226 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key352, 6), (key349, 6), (key667, 6), (key677, 6), (key667, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key506, 6), (key280, 6), (key506, 6), (key671, 6), (key520, 6), (key292, 6), (key520, 6)]

def rawRow20227 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key667, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key506, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key520, 6), (key292, 6)]

def rawRow20228 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key520, 6), (key541, 6), (key280, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key677, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6)]

def rawRow20229 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key520, 6), (key541, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6)]

def rawRow20230 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key509, 6), (key541, 6), (key280, 6), (key292, 6), (key283, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key541, 6), (key369, 6), (key677, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6)]

def rawRow20231 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key509, 6), (key541, 6), (key292, 6), (key280, 6), (key283, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key541, 6), (key677, 6), (key369, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6)]

def rawRow20232 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key506, 6), (key541, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6)]

def rawRow20233 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key506, 6), (key541, 6), (key292, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key369, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6)]

def rawRow20234 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key541, 6), (key520, 6), (key349, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key671, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6)]

def rawRow20235 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key541, 6), (key520, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6)]

def rawRow20236 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key509, 6), (key520, 6), (key349, 6), (key369, 6), (key352, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key520, 6), (key292, 6), (key671, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6)]

def rawRow20237 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key509, 6), (key520, 6), (key369, 6), (key349, 6), (key352, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key520, 6), (key671, 6), (key292, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6)]

def rawRow20238 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key506, 6), (key520, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6)]

def rawRow20239 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key506, 6), (key520, 6), (key369, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key292, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6)]

def rawRow20240 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key541, 6), (key509, 6), (key506, 6), (key520, 6), (key541, 6), (key280, 6), (key292, 6), (key349, 6), (key671, 6), (key369, 6), (key677, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6), (key667, 6)]

def rawRow20241 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key541, 6), (key509, 6), (key520, 6), (key506, 6), (key541, 6), (key292, 6), (key280, 6), (key671, 6), (key349, 6), (key677, 6), (key369, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6), (key352, 6)]

def rawRow20242 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key520, 6), (key509, 6), (key506, 6), (key541, 6), (key520, 6), (key349, 6), (key369, 6), (key280, 6), (key677, 6), (key292, 6), (key671, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6), (key667, 6)]

def rawRow20243 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key520, 6), (key509, 6), (key541, 6), (key506, 6), (key520, 6), (key369, 6), (key349, 6), (key677, 6), (key280, 6), (key671, 6), (key292, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6), (key283, 6)]

def rawRow20244 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key506, 6), (key509, 6), (key520, 6), (key541, 6), (key506, 6), (key671, 6), (key677, 6), (key292, 6), (key369, 6), (key280, 6), (key349, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6), (key352, 6)]

def rawRow20245 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key506, 6), (key509, 6), (key541, 6), (key520, 6), (key506, 6), (key677, 6), (key671, 6), (key369, 6), (key292, 6), (key349, 6), (key280, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6), (key283, 6)]

def rawRow20246 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key541, 6), (key506, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6)]

def rawRow20247 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key541, 6), (key506, 6), (key671, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key349, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6)]

def rawRow20248 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key520, 6), (key506, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6)]

def rawRow20249 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key520, 6), (key506, 6), (key677, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key280, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6)]

def rawRow20250 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key509, 6), (key506, 6), (key671, 6), (key677, 6), (key667, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key506, 6), (key280, 6), (key349, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6)]

def rawRow20251 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key509, 6), (key506, 6), (key677, 6), (key671, 6), (key667, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key506, 6), (key349, 6), (key280, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6)]

def rawRow20252 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key283, 6), (key292, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key369, 6), (key541, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key506, 6)]

def rawRow20253 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key667, 6), (key677, 6), (key283, 6), (key292, 6), (key283, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key541, 6), (key369, 6), (key541, 6), (key280, 6), (key506, 6), (key349, 6), (key506, 6)]

def rawRow20254 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key283, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key541, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key506, 6), (key349, 6)]

def rawRow20255 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key352, 6), (key369, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key292, 6), (key520, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key506, 6)]

def rawRow20256 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key667, 6), (key671, 6), (key352, 6), (key369, 6), (key352, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key520, 6), (key292, 6), (key520, 6), (key349, 6), (key506, 6), (key280, 6), (key506, 6)]

def rawRow20257 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key352, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key520, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key506, 6), (key280, 6)]

def rawRow20258 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key677, 6), (key667, 6), (key509, 6), (key520, 6), (key541, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key283, 6), (key352, 6), (key509, 6), (key506, 6), (key280, 6), (key349, 6), (key506, 6)]

def rawRow20259 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key677, 6), (key667, 6), (key520, 6), (key509, 6), (key541, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key283, 6), (key509, 6), (key352, 6), (key506, 6), (key280, 6), (key506, 6), (key349, 6)]

def rawRow20260 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key671, 6), (key667, 6), (key509, 6), (key541, 6), (key520, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key352, 6), (key283, 6), (key509, 6), (key506, 6), (key349, 6), (key280, 6), (key506, 6)]

def rawRow20261 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key671, 6), (key667, 6), (key541, 6), (key509, 6), (key520, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key352, 6), (key509, 6), (key283, 6), (key506, 6), (key349, 6), (key506, 6), (key280, 6)]

def rawRow20262 : Integer.Sparse Key := [(key671, 6), (key677, 6), (key667, 6), (key667, 6), (key520, 6), (key541, 6), (key509, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key509, 6), (key283, 6), (key352, 6), (key506, 6), (key506, 6), (key280, 6), (key349, 6)]

def rawRow20263 : Integer.Sparse Key := [(key677, 6), (key671, 6), (key667, 6), (key667, 6), (key541, 6), (key520, 6), (key509, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key509, 6), (key352, 6), (key283, 6), (key506, 6), (key506, 6), (key349, 6), (key280, 6)]

def rawRow20264 : Integer.Sparse Key := [(key236, 2), (key241, 2), (key241, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key277, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key346, 2), (key346, 2), (key347, 2), (key385, 2), (key390, 2), (key385, 2), (key400, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2), (key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2)]

def rawRow20265 : Integer.Sparse Key := [(key241, 2), (key236, 2), (key241, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key277, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key346, 2), (key347, 2), (key346, 2), (key390, 2), (key385, 2), (key400, 2), (key385, 2), (key400, 2), (key390, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2), (key655, 2), (key656, 2), (key655, 2), (key657, 2), (key658, 2), (key657, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2)]

def rawRow20266 : Integer.Sparse Key := [(key241, 2), (key241, 2), (key236, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key278, 2), (key277, 2), (key277, 2), (key307, 2), (key307, 2), (key302, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key346, 2), (key346, 2), (key400, 2), (key400, 2), (key390, 2), (key390, 2), (key385, 2), (key385, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2), (key656, 2), (key655, 2), (key655, 2), (key658, 2), (key657, 2), (key657, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2)]

def rawRow20267 : Integer.Sparse Key := [(key248, 2), (key253, 2), (key263, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key241, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key346, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key307, 2), (key321, 2), (key331, 2), (key406, 2), (key411, 2), (key435, 2), (key445, 2), (key487, 2), (key488, 2), (key385, 2), (key390, 2), (key435, 2), (key453, 2), (key487, 2), (key489, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2), (key657, 2), (key660, 2), (key661, 2), (key655, 2), (key660, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2)]

def rawRow20268 : Integer.Sparse Key := [(key253, 2), (key248, 2), (key263, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key241, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key346, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key307, 2), (key331, 2), (key321, 2), (key411, 2), (key406, 2), (key445, 2), (key435, 2), (key488, 2), (key487, 2), (key390, 2), (key385, 2), (key453, 2), (key435, 2), (key489, 2), (key487, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key660, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2)]

def rawRow20269 : Integer.Sparse Key := [(key248, 2), (key263, 2), (key253, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key253, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key321, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key321, 2), (key307, 2), (key331, 2), (key435, 2), (key487, 2), (key406, 2), (key488, 2), (key411, 2), (key445, 2), (key435, 2), (key487, 2), (key385, 2), (key489, 2), (key390, 2), (key453, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2), (key660, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2)]

def rawRow20270 : Integer.Sparse Key := [(key263, 2), (key248, 2), (key253, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key253, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key321, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key321, 2), (key331, 2), (key307, 2), (key487, 2), (key435, 2), (key488, 2), (key406, 2), (key445, 2), (key411, 2), (key487, 2), (key435, 2), (key489, 2), (key385, 2), (key453, 2), (key390, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2)]

def rawRow20271 : Integer.Sparse Key := [(key253, 2), (key263, 2), (key248, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key263, 2), (key241, 2), (key253, 2), (key321, 2), (key346, 2), (key316, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key331, 2), (key307, 2), (key321, 2), (key445, 2), (key488, 2), (key411, 2), (key487, 2), (key406, 2), (key435, 2), (key453, 2), (key489, 2), (key390, 2), (key487, 2), (key385, 2), (key435, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2)]

def rawRow20272 : Integer.Sparse Key := [(key263, 2), (key253, 2), (key248, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key263, 2), (key253, 2), (key241, 2), (key346, 2), (key321, 2), (key316, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key331, 2), (key321, 2), (key307, 2), (key488, 2), (key445, 2), (key487, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key487, 2), (key390, 2), (key435, 2), (key385, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2), (key661, 2), (key660, 2), (key657, 2), (key662, 2), (key660, 2), (key655, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2)]

def rawRow20273 : Integer.Sparse Key := [(key277, 2), (key277, 2), (key278, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key236, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key346, 2), (key346, 2), (key302, 2), (key316, 2), (key316, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key489, 2), (key489, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key488, 2), (key488, 2), (key390, 2), (key390, 2), (key411, 2), (key411, 2), (key487, 2), (key487, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2), (key658, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key655, 2), (key655, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2)]

def rawRow20274 : Integer.Sparse Key := [(key277, 2), (key278, 2), (key277, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key248, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key331, 2), (key321, 2), (key346, 2), (key307, 2), (key346, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key453, 2), (key489, 2), (key421, 2), (key489, 2), (key421, 2), (key453, 2), (key445, 2), (key488, 2), (key400, 2), (key488, 2), (key400, 2), (key445, 2), (key411, 2), (key487, 2), (key390, 2), (key487, 2), (key390, 2), (key411, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2), (key662, 2), (key658, 2), (key662, 2), (key661, 2), (key656, 2), (key661, 2), (key657, 2), (key660, 2), (key655, 2), (key660, 2), (key655, 2), (key657, 2)]

def rawRow20275 : Integer.Sparse Key := [(key278, 2), (key277, 2), (key277, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key248, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key331, 2), (key346, 2), (key321, 2), (key346, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key489, 2), (key453, 2), (key489, 2), (key421, 2), (key453, 2), (key421, 2), (key488, 2), (key445, 2), (key488, 2), (key400, 2), (key445, 2), (key400, 2), (key487, 2), (key411, 2), (key487, 2), (key390, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2), (key662, 2), (key662, 2), (key658, 2), (key661, 2), (key661, 2), (key656, 2), (key660, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key655, 2)]

def rawRow20276 : Integer.Sparse Key := [(key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key346, 2), (key321, 2), (key346, 2), (key331, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key241, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key657, 2), (key657, 2), (key658, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key347, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2)]

def rawRow20277 : Integer.Sparse Key := [(key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key346, 2), (key316, 2), (key346, 2), (key321, 2), (key331, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key241, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key657, 2), (key658, 2), (key657, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2), (key277, 2), (key278, 2), (key277, 2), (key346, 2), (key347, 2), (key346, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2)]

def rawRow20278 : Integer.Sparse Key := [(key307, 2), (key307, 2), (key302, 2), (key346, 2), (key346, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key236, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key658, 2), (key657, 2), (key657, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2), (key278, 2), (key277, 2), (key277, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2)]

def rawRow20279 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key307, 2), (key321, 2), (key346, 2), (key406, 2), (key411, 2), (key421, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key241, 2), (key411, 2), (key421, 2), (key316, 2), (key321, 2), (key435, 2), (key445, 2), (key660, 2), (key661, 2), (key248, 2), (key253, 2), (key435, 2), (key453, 2), (key660, 2), (key662, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2), (key346, 2), (key487, 2), (key488, 2), (key277, 2), (key487, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2)]

def rawRow20280 : Integer.Sparse Key := [(key321, 2), (key316, 2), (key331, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key307, 2), (key346, 2), (key321, 2), (key411, 2), (key406, 2), (key421, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key241, 2), (key421, 2), (key411, 2), (key321, 2), (key316, 2), (key445, 2), (key435, 2), (key661, 2), (key660, 2), (key253, 2), (key248, 2), (key453, 2), (key435, 2), (key662, 2), (key660, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key487, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2)]

def rawRow20281 : Integer.Sparse Key := [(key316, 2), (key331, 2), (key321, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key321, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key411, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key411, 2), (key241, 2), (key421, 2), (key435, 2), (key660, 2), (key316, 2), (key661, 2), (key321, 2), (key445, 2), (key435, 2), (key660, 2), (key248, 2), (key662, 2), (key253, 2), (key453, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2), (key487, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2)]

def rawRow20282 : Integer.Sparse Key := [(key331, 2), (key316, 2), (key321, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key321, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key411, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key411, 2), (key421, 2), (key241, 2), (key660, 2), (key435, 2), (key661, 2), (key316, 2), (key445, 2), (key321, 2), (key660, 2), (key435, 2), (key662, 2), (key248, 2), (key453, 2), (key253, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2)]

def rawRow20283 : Integer.Sparse Key := [(key321, 2), (key331, 2), (key316, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key346, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key406, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key421, 2), (key241, 2), (key411, 2), (key445, 2), (key661, 2), (key321, 2), (key660, 2), (key316, 2), (key435, 2), (key453, 2), (key662, 2), (key253, 2), (key660, 2), (key248, 2), (key435, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2)]

def rawRow20284 : Integer.Sparse Key := [(key331, 2), (key321, 2), (key316, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key346, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key406, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key421, 2), (key411, 2), (key241, 2), (key661, 2), (key445, 2), (key660, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key660, 2), (key253, 2), (key435, 2), (key248, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2), (key488, 2), (key487, 2), (key346, 2), (key489, 2), (key487, 2), (key277, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2)]

def rawRow20285 : Integer.Sparse Key := [(key346, 2), (key346, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key302, 2), (key316, 2), (key316, 2), (key657, 2), (key657, 2), (key658, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key236, 2), (key406, 2), (key406, 2), (key331, 2), (key331, 2), (key453, 2), (key453, 2), (key662, 2), (key662, 2), (key263, 2), (key263, 2), (key445, 2), (key445, 2), (key661, 2), (key661, 2), (key253, 2), (key253, 2), (key321, 2), (key321, 2), (key660, 2), (key660, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2), (key347, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key277, 2), (key277, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2)]

def rawRow20286 : Integer.Sparse Key := [(key346, 2), (key347, 2), (key346, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key657, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key406, 2), (key236, 2), (key406, 2), (key453, 2), (key662, 2), (key331, 2), (key662, 2), (key331, 2), (key453, 2), (key445, 2), (key661, 2), (key263, 2), (key661, 2), (key263, 2), (key445, 2), (key321, 2), (key660, 2), (key253, 2), (key660, 2), (key253, 2), (key321, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2), (key489, 2), (key347, 2), (key489, 2), (key488, 2), (key278, 2), (key488, 2), (key346, 2), (key487, 2), (key277, 2), (key487, 2), (key277, 2), (key346, 2)]

def rawRow20287 : Integer.Sparse Key := [(key347, 2), (key346, 2), (key346, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key657, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key406, 2), (key406, 2), (key236, 2), (key662, 2), (key453, 2), (key662, 2), (key331, 2), (key453, 2), (key331, 2), (key661, 2), (key445, 2), (key661, 2), (key263, 2), (key445, 2), (key263, 2), (key660, 2), (key321, 2), (key660, 2), (key253, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2), (key489, 2), (key489, 2), (key347, 2), (key488, 2), (key488, 2), (key278, 2), (key487, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key277, 2)]

def rawRow20288 : Integer.Sparse Key := [(key385, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key435, 2), (key487, 2), (key445, 2), (key488, 2), (key421, 2), (key453, 2), (key489, 2), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key435, 2), (key660, 2), (key445, 2), (key661, 2), (key331, 2), (key453, 2), (key662, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2), (key241, 2), (key253, 2), (key263, 2), (key307, 2), (key321, 2), (key331, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2)]

def rawRow20289 : Integer.Sparse Key := [(key390, 2), (key385, 2), (key400, 2), (key411, 2), (key406, 2), (key487, 2), (key435, 2), (key488, 2), (key445, 2), (key421, 2), (key489, 2), (key453, 2), (key253, 2), (key248, 2), (key263, 2), (key321, 2), (key316, 2), (key660, 2), (key435, 2), (key661, 2), (key445, 2), (key331, 2), (key662, 2), (key453, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2), (key241, 2), (key263, 2), (key253, 2), (key307, 2), (key331, 2), (key321, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2)]

def rawRow20290 : Integer.Sparse Key := [(key385, 2), (key400, 2), (key390, 2), (key435, 2), (key445, 2), (key406, 2), (key488, 2), (key411, 2), (key487, 2), (key453, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key253, 2), (key435, 2), (key445, 2), (key316, 2), (key661, 2), (key321, 2), (key660, 2), (key453, 2), (key331, 2), (key662, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2), (key253, 2), (key241, 2), (key263, 2), (key321, 2), (key307, 2), (key331, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2)]

def rawRow20291 : Integer.Sparse Key := [(key400, 2), (key385, 2), (key390, 2), (key445, 2), (key435, 2), (key488, 2), (key406, 2), (key487, 2), (key411, 2), (key453, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key253, 2), (key445, 2), (key435, 2), (key661, 2), (key316, 2), (key660, 2), (key321, 2), (key453, 2), (key662, 2), (key331, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2), (key253, 2), (key263, 2), (key241, 2), (key321, 2), (key331, 2), (key307, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2)]

def rawRow20292 : Integer.Sparse Key := [(key390, 2), (key400, 2), (key385, 2), (key487, 2), (key488, 2), (key411, 2), (key445, 2), (key406, 2), (key435, 2), (key489, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key248, 2), (key660, 2), (key661, 2), (key321, 2), (key445, 2), (key316, 2), (key435, 2), (key662, 2), (key331, 2), (key453, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2), (key263, 2), (key241, 2), (key253, 2), (key331, 2), (key307, 2), (key321, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2)]

def rawRow20293 : Integer.Sparse Key := [(key400, 2), (key390, 2), (key385, 2), (key488, 2), (key487, 2), (key445, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key248, 2), (key661, 2), (key660, 2), (key445, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key331, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2), (key263, 2), (key253, 2), (key241, 2), (key331, 2), (key321, 2), (key307, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2)]

def rawRow20294 : Integer.Sparse Key := [(key406, 2), (key411, 2), (key421, 2), (key385, 2), (key390, 2), (key435, 2), (key487, 2), (key453, 2), (key489, 2), (key400, 2), (key445, 2), (key488, 2), (key316, 2), (key321, 2), (key331, 2), (key248, 2), (key253, 2), (key435, 2), (key660, 2), (key453, 2), (key662, 2), (key263, 2), (key445, 2), (key661, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2), (key307, 2), (key390, 2), (key400, 2), (key241, 2), (key411, 2), (key421, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2)]

def rawRow20295 : Integer.Sparse Key := [(key411, 2), (key406, 2), (key421, 2), (key390, 2), (key385, 2), (key487, 2), (key435, 2), (key489, 2), (key453, 2), (key400, 2), (key488, 2), (key445, 2), (key321, 2), (key316, 2), (key331, 2), (key253, 2), (key248, 2), (key660, 2), (key435, 2), (key662, 2), (key453, 2), (key263, 2), (key661, 2), (key445, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2), (key307, 2), (key400, 2), (key390, 2), (key241, 2), (key421, 2), (key411, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2)]

def rawRow20296 : Integer.Sparse Key := [(key406, 2), (key421, 2), (key411, 2), (key435, 2), (key453, 2), (key385, 2), (key489, 2), (key390, 2), (key487, 2), (key445, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key321, 2), (key435, 2), (key453, 2), (key248, 2), (key662, 2), (key253, 2), (key660, 2), (key445, 2), (key263, 2), (key661, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2), (key390, 2), (key307, 2), (key400, 2), (key411, 2), (key241, 2), (key421, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2)]

def rawRow20297 : Integer.Sparse Key := [(key421, 2), (key406, 2), (key411, 2), (key453, 2), (key435, 2), (key489, 2), (key385, 2), (key487, 2), (key390, 2), (key445, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key321, 2), (key453, 2), (key435, 2), (key662, 2), (key248, 2), (key660, 2), (key253, 2), (key445, 2), (key661, 2), (key263, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2), (key390, 2), (key400, 2), (key307, 2), (key411, 2), (key421, 2), (key241, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1973 : Integer.Sparse Key := [(key1218, -2), (key1181, -2), (key1181, -2), (key1181, 6), (key1162, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key977, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

def rawRow1974 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2369, 2), (key2384, 2), (key2397, 6), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, -2), (key2463, -2), (key2474, -2), (key2463, 2), (key2463, 2), (key2497, 2)]

def rawRow1975 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2384, 2), (key2369, 2), (key2397, 6), (key2397, -2), (key2431, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, 2), (key2497, 2), (key2463, 2)]

def rawRow1976 : Integer.Sparse Key := [(key2369, -6), (key2384, 2), (key2369, 2), (key2369, 2), (key2397, 6), (key2431, -2), (key2397, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, 2), (key2463, 2), (key2463, 2)]

def rawRow1978 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2369, 6), (key2463, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, 2), (key2397, 2), (key2431, 2)]

def rawRow1979 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2369, 6), (key2463, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, 2), (key2431, 2), (key2397, 2)]

def rawRow1980 : Integer.Sparse Key := [(key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2369, 6), (key2497, -2), (key2463, -2), (key2463, -2), (key2384, -2), (key2369, -2), (key2369, -2), (key2431, 2), (key2397, 2), (key2397, 2)]

def rawRow1981 : Integer.Sparse Key := [(key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2497, 6), (key2369, -2), (key2463, -2), (key2463, -2), (key2431, -2), (key2497, -2), (key2497, -2), (key2384, 2), (key2474, 2), (key2474, 2)]

def rawRow1982 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2497, 6), (key2463, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, 2), (key2384, 2), (key2474, 2)]

def rawRow1983 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2497, 6), (key2463, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, 2), (key2474, 2), (key2384, 2)]

def rawRow1985 : Integer.Sparse Key := [(key2497, -6), (key2431, 2), (key2497, 2), (key2497, 2), (key2474, 6), (key2384, -2), (key2474, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, 2), (key2463, 2), (key2463, 2)]

def rawRow1986 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2431, 2), (key2497, 2), (key2474, 6), (key2474, -2), (key2384, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, 2), (key2369, 2), (key2463, 2)]

def rawRow1987 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2497, 2), (key2431, 2), (key2474, 6), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, -2), (key2463, -2), (key2397, -2), (key2463, 2), (key2463, 2), (key2369, 2)]

def rawRow1988 : Integer.Sparse Key := [(key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1532, 2), (key1532, 2), (key1766, 2), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1610, -1), (key1649, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1807, -1), (key1638, -2), (key1638, -2), (key1830, -2), (key1638, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1672, 1), (key1830, 1)]

def rawRow1989 : Integer.Sparse Key := [(key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1532, 2), (key1766, 2), (key1532, 2), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, -1), (key1610, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1638, -2), (key1830, -2), (key1638, -2), (key1672, 1), (key1638, 1), (key1830, 1), (key1638, 1), (key1830, 1), (key1672, 1)]

def rawRow1990 : Integer.Sparse Key := [(key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1766, 2), (key1532, 2), (key1532, 2), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, -1), (key1807, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1830, -2), (key1638, -2), (key1638, -2), (key1830, 1), (key1830, 1), (key1672, 1), (key1672, 1), (key1638, 1), (key1638, 1)]

def rawRow1992 : Integer.Sparse Key := [(key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1638, 2), (key1638, 2), (key1830, 2), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1), (key1638, -1), (key1672, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1830, -1), (key1532, -2), (key1532, -2), (key1766, -2), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

def rawRow1993 : Integer.Sparse Key := [(key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1638, 2), (key1830, 2), (key1638, 2), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1672, -1), (key1638, -1), (key1830, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1532, -2), (key1766, -2), (key1532, -2), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

def rawRow1994 : Integer.Sparse Key := [(key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1830, 2), (key1638, 2), (key1638, 2), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1), (key1830, -1), (key1830, -1), (key1672, -1), (key1672, -1), (key1638, -1), (key1638, -1), (key1766, -2), (key1532, -2), (key1532, -2), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

def rawRow1995 : Integer.Sparse Key := [(key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1252, 2), (key1605, 2), (key1605, 2), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1), (key1252, -1), (key1252, -1), (key1527, -1), (key1527, -1), (key1605, -1), (key1605, -1), (key1266, -2), (key1649, -2), (key1649, -2), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

def rawRow1996 : Integer.Sparse Key := [(key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1605, 2), (key1252, 2), (key1605, 2), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1527, -1), (key1605, -1), (key1252, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1649, -2), (key1266, -2), (key1649, -2), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

def rawRow1997 : Integer.Sparse Key := [(key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1605, 2), (key1605, 2), (key1252, 2), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1), (key1605, -1), (key1527, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1252, -1), (key1649, -2), (key1649, -2), (key1266, -2), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

def rawRow1999 : Integer.Sparse Key := [(key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1266, 2), (key1649, 2), (key1649, 2), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, -1), (key1257, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1252, -2), (key1605, -2), (key1605, -2), (key1252, 1), (key1252, 1), (key1527, 1), (key1527, 1), (key1605, 1), (key1605, 1)]

def rawRow2000 : Integer.Sparse Key := [(key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1649, 2), (key1266, 2), (key1649, 2), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, -1), (key1610, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1605, -2), (key1252, -2), (key1605, -2), (key1527, 1), (key1605, 1), (key1252, 1), (key1605, 1), (key1252, 1), (key1527, 1)]

def rawRow2001 : Integer.Sparse Key := [(key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1649, 2), (key1649, 2), (key1266, 2), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1610, -1), (key1532, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1257, -1), (key1605, -2), (key1605, -2), (key1252, -2), (key1605, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1527, 1), (key1252, 1)]

def rawRow2002 : Integer.Sparse Key := [(key3034, -2), (key3041, -2), (key3041, -2), (key3037, 2), (key3041, 2), (key3041, 2), (key3121, 2), (key3133, 2), (key3133, 2), (key3133, -6), (key3129, -2), (key3139, -2), (key3139, -2), (key3139, 6)]

def rawRow2003 : Integer.Sparse Key := [(key3041, -2), (key3034, -2), (key3041, -2), (key3041, 2), (key3037, 2), (key3041, 2), (key3133, 2), (key3121, 2), (key3133, 2), (key3133, -6), (key3139, -2), (key3129, -2), (key3139, -2), (key3139, 6)]

def rawRow2004 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3034, -2), (key3041, 2), (key3041, 2), (key3037, 2), (key3133, 2), (key3133, 2), (key3121, 2), (key3133, -6), (key3139, -2), (key3139, -2), (key3129, -2), (key3139, 6)]

def rawRow2006 : Integer.Sparse Key := [(key3121, -2), (key3133, -2), (key3133, -2), (key3129, 2), (key3139, 2), (key3139, 2), (key3034, 2), (key3041, 2), (key3041, 2), (key3139, -6), (key3037, -2), (key3041, -2), (key3041, -2), (key3133, 6)]

def rawRow2007 : Integer.Sparse Key := [(key3133, -2), (key3121, -2), (key3133, -2), (key3139, 2), (key3129, 2), (key3139, 2), (key3041, 2), (key3034, 2), (key3041, 2), (key3139, -6), (key3041, -2), (key3037, -2), (key3041, -2), (key3133, 6)]

def rawRow2008 : Integer.Sparse Key := [(key3133, -2), (key3133, -2), (key3121, -2), (key3139, 2), (key3139, 2), (key3129, 2), (key3041, 2), (key3041, 2), (key3034, 2), (key3139, -6), (key3041, -2), (key3041, -2), (key3037, -2), (key3133, 6)]

def rawRow2009 : Integer.Sparse Key := [(key3037, -2), (key3037, -2), (key3129, -2), (key3034, 2), (key3034, 2), (key3121, 2), (key3041, 2), (key3041, 2), (key3139, 2), (key3034, -6), (key3041, -2), (key3041, -2), (key3133, -2), (key3037, 6)]

def rawRow2010 : Integer.Sparse Key := [(key3037, -2), (key3129, -2), (key3037, -2), (key3034, 2), (key3121, 2), (key3034, 2), (key3041, 2), (key3139, 2), (key3041, 2), (key3034, -6), (key3041, -2), (key3133, -2), (key3041, -2), (key3037, 6)]

def rawRow2011 : Integer.Sparse Key := [(key3129, -2), (key3037, -2), (key3037, -2), (key3121, 2), (key3034, 2), (key3034, 2), (key3139, 2), (key3041, 2), (key3041, 2), (key3034, -6), (key3133, -2), (key3041, -2), (key3041, -2), (key3037, 6)]

def rawRow2013 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3139, -2), (key3041, 2), (key3041, 2), (key3133, 2), (key3037, 2), (key3037, 2), (key3129, 2), (key3037, -6), (key3034, -2), (key3034, -2), (key3121, -2), (key3034, 6)]

def rawRow2014 : Integer.Sparse Key := [(key3041, -2), (key3139, -2), (key3041, -2), (key3041, 2), (key3133, 2), (key3041, 2), (key3037, 2), (key3129, 2), (key3037, 2), (key3037, -6), (key3034, -2), (key3121, -2), (key3034, -2), (key3034, 6)]

def rawRow2015 : Integer.Sparse Key := [(key3139, -2), (key3041, -2), (key3041, -2), (key3133, 2), (key3041, 2), (key3041, 2), (key3129, 2), (key3037, 2), (key3037, 2), (key3037, -6), (key3121, -2), (key3034, -2), (key3034, -2), (key3034, 6)]

def rawRow2016 : Integer.Sparse Key := [(key1252, -2), (key1257, -2), (key1257, -2), (key1252, 1), (key1257, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1266, 1), (key1527, 2), (key1532, 2), (key1532, 2), (key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1605, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1649, -1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1)]

def rawRow2017 : Integer.Sparse Key := [(key1257, -2), (key1252, -2), (key1257, -2), (key1257, 1), (key1252, 1), (key1266, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1532, 2), (key1527, 2), (key1532, 2), (key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1)]

def rawRow2018 : Integer.Sparse Key := [(key1257, -2), (key1257, -2), (key1252, -2), (key1266, 1), (key1266, 1), (key1257, 1), (key1257, 1), (key1252, 1), (key1252, 1), (key1532, 2), (key1532, 2), (key1527, 2), (key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1)]

def rawRow2020 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1252, 2), (key1257, 2), (key1257, 2), (key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1252, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1266, -1), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1)]

def rawRow2021 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1257, 2), (key1252, 2), (key1257, 2), (key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1)]

def rawRow2022 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1257, 2), (key1257, 2), (key1252, 2), (key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1266, -1), (key1266, -1), (key1257, -1), (key1257, -1), (key1252, -1), (key1252, -1), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1)]

def rawRow2023 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1807, 2), (key1807, 2), (key1830, 2), (key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1766, -1), (key1766, -1), (key1807, -1), (key1807, -1), (key1830, -1), (key1830, -1), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1)]

def rawRow2024 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1807, 2), (key1830, 2), (key1807, 2), (key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1)]

def rawRow2025 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1830, 2), (key1807, 2), (key1807, 2), (key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1830, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1766, -1), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1)]

def rawRow2027 : Integer.Sparse Key := [(key1807, -2), (key1807, -2), (key1830, -2), (key1766, 1), (key1766, 1), (key1807, 1), (key1807, 1), (key1830, 1), (key1830, 1), (key1649, 2), (key1649, 2), (key1672, 2), (key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1)]

def rawRow2028 : Integer.Sparse Key := [(key1807, -2), (key1830, -2), (key1807, -2), (key1807, 1), (key1830, 1), (key1766, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1649, 2), (key1672, 2), (key1649, 2), (key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1)]

def rawRow2029 : Integer.Sparse Key := [(key1830, -2), (key1807, -2), (key1807, -2), (key1830, 1), (key1807, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1766, 1), (key1672, 2), (key1649, 2), (key1649, 2), (key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1638, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1532, -1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined161_part2 : Sparse := [([1, 1, -1, 1, 1, -1, -1], -18)]

end MUB6.TaoCertificate

end OAI
end


