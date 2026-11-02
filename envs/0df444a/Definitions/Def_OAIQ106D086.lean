-- Prove2me | Definitions.Def_OAIQ106D086
-- name    : OAIQ106D086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:53:28.236587+00:00
-- url     : https://prove2.me/theorems/eec89910-6f64-44bf-928e-ae64ad7a22d1
-- title:
--   Definitions bundle OAIQ106D086 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1026 declarations of OpenAI's Lean: 1026 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key103`, `OAI.MUB6.Certificate.GramRows.key113`, `OAI.MUB6.Certificate.GramRows.key1290`, `OAI.MUB6.Certificate.GramRows.key1310`, `OAI.MUB6.Certificate.GramRows.key1322`, `OAI.MUB6.Certificate.GramRows.key136`, `OAI.MUB6.Certificate.GramRows.key1385`, `OAI.MUB6.Certificate.GramRows.key1418`, `OAI.MUB6.Certificate.GramRows.key1440`, `OAI.MUB6.Certificate.GramRows.key1583`, `OAI.MUB6.Certificate.GramRows.key1587`, `OAI.MUB6.Certificate.GramRows.key1687`, `OAI.MUB6.Certificate.GramRows.key181`, `OAI.MUB6.Certificate.GramRows.key19`, `OAI.MUB6.Certificate.GramRows.key1907`, `OAI.MUB6.Certificate.GramRows.key1909`, `OAI.MUB6.Certificate.GramRows.key1924`, `OAI.MUB6.Certificate.GramRows.key252`, `OAI.MUB6.Certificate.GramRows.key389`, `OAI.MUB6.Certificate.GramRows.key429`, `OAI.MUB6.Certificate.GramRows.key443`, `OAI.MUB6.Certificate.GramRows.key452`, `OAI.MUB6.Certificate.GramRows.key500`, `OAI.MUB6.Certificate.GramRows.key511`, `OAI.MUB6.Certificate.GramRows.key71`, `OAI.MUB6.Certificate.GramRows.key73`, `OAI.MUB6.Certificate.GramRows.row3770`, `OAI.MUB6.Certificate.GramRows.row3771`, `OAI.MUB6.Certificate.GramRows.row3772`, `OAI.MUB6.Certificate.GramRows.row3785`, `OAI.MUB6.Certificate.GramRows.row3786`, `OAI.MUB6.Certificate.GramRows.row3787`, `OAI.MUB6.Certificate.GramRows.row3824`, `OAI.MUB6.Certificate.GramRows.row3825`, `OAI.MUB6.Certificate.GramRows.row3826`, `OAI.MUB6.Certificate.GramRows.row3827`, `OAI.MUB6.Certificate.GramRows.row3828`, `OAI.MUB6.Certificate.GramRows.row3829`, `OAI.MUB6.Certificate.GramRows.row3830`, `OAI.MUB6.Certificate.GramRows.row3831` and 986 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramRows_Block17`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block54`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_GramRows_Block57`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block59`, `MutuallyUnbiased_GramRows_Block60`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`, `MutuallyUnbiased_GramRows_Block63`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D143`, `OAIQ106D144`, `OAIQ106D145`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172` and `OAIQ106D174`.
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

def key19 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key71 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, -2), (2, 2)]⟩
def key73 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key103 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key113 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 1), (1, 1), (2, 0)]⟩

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

def key136 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 2), (2, -2)]⟩
def key181 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key252 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 2), (2, 0)]⟩

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

def key1290 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key1310 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key1322 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key1385 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩

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

def key1418 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (2, 3)]⟩
def key1440 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩

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

def key1583 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key1587 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 2), (1, -1), (2, 1)]⟩

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

def key1687 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (1, -1), (2, 1)]⟩

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

def key1907 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (1, 0), (2, 1)]⟩
def key1909 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, 0), (1, -1), (2, 1)]⟩

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

def key1924 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (1, -1), (2, 1)]⟩

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

def key389 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key429 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 2)]⟩
def key443 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 1), (1, 1), (2, 0)]⟩
def key452 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -2)]⟩
def key500 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key511 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 2), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row660 : Integer.Sparse Key := [(key1422, -6), (key1453, 6), (key1571, 6), (key1653, -6), (key1786, -6), (key1811, 6)]

def row661 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row662 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row663 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row664 : Integer.Sparse Key := [(key1422, 6), (key1453, -6), (key1571, -6), (key1653, 6), (key1786, 6), (key1811, -6)]

def row665 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row666 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row667 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row668 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row669 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row670 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row671 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

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

def row672 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row673 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row674 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key300, 6), (key314, -6), (key383, -6), (key404, 6)]

def row675 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row676 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row677 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row678 : Integer.Sparse Key := [(key234, 6), (key246, -6), (key300, -6), (key314, 12), (key404, -6)]

def row679 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row680 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row681 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row682 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row683 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row684 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row685 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row686 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row687 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

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

def row3770 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3771 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3772 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3785 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3786 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3787 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3824 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3825 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3826 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3827 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3828 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3829 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3830 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3831 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3832 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3833 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3834 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3835 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3836 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3837 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3838 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3839 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3840 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3841 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3842 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3843 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3844 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3845 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3846 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3847 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3848 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3849 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3850 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3851 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3852 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3853 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3854 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3855 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3856 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3857 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3858 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3859 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3860 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3861 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3862 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3863 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3864 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3865 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3866 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3867 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3868 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3869 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3870 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3871 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3872 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3873 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3874 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3875 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3876 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3877 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3878 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3879 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3880 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3881 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3882 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3883 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3884 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3885 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3886 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3887 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3888 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3889 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3890 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3891 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3892 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3893 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3894 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3895 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3896 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3897 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3898 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3899 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3900 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3901 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3902 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3903 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3904 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3905 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3906 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3907 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3908 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3909 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3910 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3911 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3912 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3913 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3914 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3915 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3916 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3917 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3918 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3919 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3920 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3921 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3922 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3923 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3924 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3925 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3926 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3927 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3928 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3929 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3930 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3931 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3932 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3933 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3934 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3935 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3936 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3937 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3938 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3939 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3940 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3941 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3942 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3943 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3944 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3945 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3946 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3947 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3948 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3949 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3950 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3951 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3952 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3953 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3954 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3955 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3956 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3957 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3958 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3959 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3960 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3961 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3962 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3963 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key429, 2), (key457, -6)]

def row3964 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key429, 2), (key457, -6)]

def row3965 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

def row3966 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

def row3967 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

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

def row3968 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

def row3969 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

def row3970 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

def row3971 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

def row3972 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2)]

def row3973 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2)]

def row3980 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3981 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3982 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3995 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row3996 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row3997 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

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

def row4160 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4161 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4162 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4175 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4176 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4177 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4184 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4185 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4186 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4187 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4188 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4189 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4190 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4191 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4192 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4193 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4194 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4195 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4196 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4197 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4198 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4199 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4200 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4201 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4202 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4203 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4204 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4205 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4206 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4207 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4208 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4209 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4210 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4211 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4212 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4213 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4214 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4215 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4216 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4217 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4218 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4219 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4220 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4221 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4222 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4223 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4224 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4225 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4226 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4227 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4228 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4229 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4230 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4231 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4232 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4233 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4234 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4235 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4236 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4237 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4238 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4239 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4240 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4241 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4242 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4243 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4244 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4245 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4246 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4247 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4248 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4249 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4250 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4251 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4252 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4253 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4254 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4255 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4256 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4257 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4258 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4259 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4260 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4261 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4262 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4263 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4264 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4265 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4266 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4267 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4268 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4269 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4270 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4271 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4272 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4273 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4274 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4275 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4276 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4277 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4278 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4279 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4280 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4281 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4282 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4283 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4284 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4285 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4286 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4287 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4288 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4289 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4290 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4291 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4292 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4293 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4294 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4295 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4296 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4297 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4298 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4299 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4300 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4301 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4302 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4303 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4304 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4305 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4306 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4307 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4310 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4311 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4312 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4313 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4314 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4315 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4316 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4317 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4318 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4319 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4320 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4321 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4322 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4323 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4324 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4325 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4326 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4327 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4328 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4329 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4330 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4331 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4332 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4333 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4334 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4335 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4336 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4337 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4338 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4339 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4340 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4341 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4342 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4343 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4344 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4345 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4346 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4347 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4348 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4349 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4350 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4351 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4352 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4353 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4354 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4355 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4356 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4357 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4358 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4359 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4360 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4361 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4362 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4363 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4364 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4365 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4366 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4367 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4368 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4369 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4370 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4371 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4372 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4373 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4374 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4375 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4382 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

def row4383 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

def row4384 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

def row4385 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

def row4386 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2)]

def row4387 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2)]

def row4388 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4389 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4390 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4391 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4392 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4393 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4394 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4395 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4396 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4397 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4398 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4399 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4400 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4401 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4402 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4403 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4404 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4405 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4406 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4407 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4408 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4409 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4410 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4411 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4412 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4413 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4414 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4415 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4416 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4417 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4418 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4419 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4420 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4421 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4422 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4423 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4424 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4425 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4426 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4427 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4428 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4429 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4430 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4431 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4432 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4433 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4434 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4435 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4436 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4437 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4438 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4439 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4440 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4441 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4442 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4443 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4444 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4445 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4446 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4447 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4448 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4449 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4450 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4454 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4455 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4456 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4457 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4458 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4459 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4460 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4461 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4462 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4463 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4464 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4465 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4466 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4467 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4468 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4469 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4470 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4471 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4472 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4473 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4474 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4475 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4476 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4477 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4478 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4479 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4480 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4481 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4482 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4483 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4484 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4485 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4486 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4487 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4488 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4489 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4490 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4491 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4492 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4493 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4494 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4495 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4496 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4497 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4498 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4499 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4500 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4501 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4502 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4503 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4504 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4505 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4506 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4507 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4508 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4509 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4510 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4511 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4512 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4513 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4514 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4515 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4516 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4517 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4518 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4519 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4520 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4521 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4522 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4523 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4524 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4525 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4526 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4527 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4528 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4529 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4530 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4531 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4532 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4533 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4534 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4535 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4536 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4537 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4538 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4539 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4540 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4541 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4542 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4543 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4544 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4545 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4546 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4547 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4548 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4549 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4550 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4551 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4552 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4553 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4554 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4555 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4556 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4557 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4558 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4559 : Integer.Sparse Key := [(key1492, 6), (key1496, -6), (key1718, -6), (key1728, 6), (key1865, 6), (key1870, -6)]

def row4560 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4561 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4562 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4563 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4564 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4565 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4566 : Integer.Sparse Key := [(key1492, -6), (key1496, 6), (key1718, 6), (key1728, -6), (key1865, -6), (key1870, 6)]

def row4567 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4568 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4569 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4570 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4571 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4572 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4573 : Integer.Sparse Key := [(key281, 6), (key290, -6), (key350, -6), (key367, 6), (key516, 6), (key538, -6)]

def row4574 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4575 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4576 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4577 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4578 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4579 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4580 : Integer.Sparse Key := [(key281, -6), (key290, 6), (key350, 6), (key367, -6), (key516, -6), (key538, 6)]

def row4581 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4582 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4583 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4584 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4585 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4586 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4587 : Integer.Sparse Key := [(key1367, 6), (key1376, -6), (key1493, -6), (key1515, 6), (key1725, 6), (key1743, -6)]

def row4588 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4589 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4590 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4591 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4592 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4593 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4594 : Integer.Sparse Key := [(key1367, -6), (key1376, 6), (key1493, 6), (key1515, -6), (key1725, -6), (key1743, 6)]

def row4595 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4596 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4597 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4598 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4599 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4600 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4601 : Integer.Sparse Key := [(key29, 6), (key33, -6), (key495, -6), (key554, 6), (key665, 6), (key682, -6)]

def row4602 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4603 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4604 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4605 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

def row4606 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

def row4607 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4608 : Integer.Sparse Key := [(key33, 6), (key149, -6), (key175, -6), (key185, 6), (key223, -6), (key495, 6)]

def row4609 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4610 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4611 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4612 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4613 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4614 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4615 : Integer.Sparse Key := [(key1361, 6), (key1373, -6), (key1487, -6), (key1512, 6), (key1722, 6), (key1740, -6)]

def row4616 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4617 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4618 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4619 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4620 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4621 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4622 : Integer.Sparse Key := [(key1361, -6), (key1373, 6), (key1487, 6), (key1512, -6), (key1722, -6), (key1740, 6)]

def row4623 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4624 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4625 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4626 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4627 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4628 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4629 : Integer.Sparse Key := [(key351, 6), (key354, -6), (key508, -6), (key523, 6), (key668, 6), (key672, -6)]

def row4630 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4631 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4632 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4633 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4634 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4635 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4636 : Integer.Sparse Key := [(key351, -6), (key398, 6), (key458, -6), (key470, -6), (key481, 6), (key508, 6)]

def row4637 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4638 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4639 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4640 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4641 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4642 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4643 : Integer.Sparse Key := [(key1502, 6), (key1504, -6), (key1734, -6), (key1737, 6), (key1945, 6), (key1947, -6)]

def row4644 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4645 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4646 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4647 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4648 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4649 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4650 : Integer.Sparse Key := [(key1502, -6), (key1504, 6), (key1734, 6), (key1737, -6), (key1945, -6), (key1947, 6)]

def row4651 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4652 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4653 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4654 : Integer.Sparse Key := [(key261, -3), (key285, 1), (key295, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4655 : Integer.Sparse Key := [(key257, -1), (key261, -3), (key272, 1), (key282, 1), (key285, 1), (key295, 1), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4656 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key272, 2), (key282, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4657 : Integer.Sparse Key := [(key261, 6), (key272, -6), (key354, -6), (key371, 6), (key523, 6), (key543, -6)]

def row4658 : Integer.Sparse Key := [(key261, 3), (key285, -1), (key295, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4659 : Integer.Sparse Key := [(key257, 1), (key261, 3), (key272, -1), (key282, -1), (key285, -1), (key295, -1), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4660 : Integer.Sparse Key := [(key257, 2), (key261, 2), (key272, -2), (key282, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4661 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4662 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4663 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4664 : Integer.Sparse Key := [(key261, -6), (key272, 6), (key398, 6), (key470, -6), (key573, -6), (key596, 6)]

def row4665 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4666 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4667 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4668 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4669 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4670 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4671 : Integer.Sparse Key := [(key223, 6), (key226, -6), (key495, -6), (key552, 6), (key620, 6), (key646, -6)]

def row4672 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4673 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4674 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4675 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4676 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4677 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4678 : Integer.Sparse Key := [(key223, -6), (key226, 6), (key495, 6), (key552, -6), (key620, -6), (key646, 6)]

def row4679 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4680 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4681 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4682 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4683 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4684 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4685 : Integer.Sparse Key := [(key1366, 6), (key1370, -6), (key1718, -6), (key1747, 6), (key1865, 6), (key1880, -6)]

def row4686 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4687 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4688 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4689 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4690 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4691 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4692 : Integer.Sparse Key := [(key1366, -6), (key1370, 6), (key1718, 6), (key1747, -6), (key1865, -6), (key1880, 6)]

def row4693 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4694 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4695 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4696 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4697 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4698 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4699 : Integer.Sparse Key := [(key1276, 6), (key1281, -6), (key1699, -6), (key1753, 6), (key1934, 6), (key1954, -6)]

def row4700 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4701 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4702 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4703 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4704 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4705 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4706 : Integer.Sparse Key := [(key1276, -6), (key1281, 6), (key1699, 6), (key1753, -6), (key1934, -6), (key1954, 6)]

def row4707 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4708 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4709 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4710 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4711 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4712 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4713 : Integer.Sparse Key := [(key1276, 6), (key1279, -6), (key1699, -6), (key1752, 6), (key1853, 6), (key1885, -6)]

def row4714 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4715 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4716 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4717 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4718 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4719 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4720 : Integer.Sparse Key := [(key1276, -6), (key1279, 6), (key1699, 6), (key1752, -6), (key1853, -6), (key1885, 6)]

def row4721 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4722 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4723 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4724 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4725 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4726 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4727 : Integer.Sparse Key := [(key1365, 6), (key1375, -6), (key1491, -6), (key1514, 6), (key1724, 6), (key1742, -6)]

def row4728 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4729 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4730 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4731 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4732 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4733 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4734 : Integer.Sparse Key := [(key1365, -6), (key1375, 6), (key1491, 6), (key1514, -6), (key1724, -6), (key1742, 6)]

def row4735 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4736 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4737 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4738 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4739 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4740 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4741 : Integer.Sparse Key := [(key741, 6), (key742, -6), (key900, -6), (key913, 6), (key951, 6), (key954, -6)]

def row4742 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4743 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4744 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4745 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4746 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4747 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4748 : Integer.Sparse Key := [(key741, -6), (key742, 6), (key900, 6), (key913, -6), (key951, -6), (key954, 6)]

def row4749 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4750 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4751 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4752 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4753 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4754 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4755 : Integer.Sparse Key := [(key1280, 6), (key1284, -6), (key1703, -6), (key1757, 6), (key1856, 6), (key1887, -6)]

def row4756 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4757 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4758 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4759 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4760 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4761 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4762 : Integer.Sparse Key := [(key1280, -6), (key1284, 6), (key1703, 6), (key1757, -6), (key1856, -6), (key1887, 6)]

def row4763 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4764 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4765 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4766 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4767 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4768 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4769 : Integer.Sparse Key := [(key1488, 6), (key1493, -6), (key1714, -6), (key1725, 6), (key1938, 6), (key1941, -6)]

def row4770 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4771 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4772 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4773 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4774 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4775 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4776 : Integer.Sparse Key := [(key1488, -6), (key1493, 6), (key1714, 6), (key1725, -6), (key1938, -6), (key1941, 6)]

def row4777 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4778 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4779 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4780 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4781 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4782 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4783 : Integer.Sparse Key := [(key1362, 6), (key1375, -6), (key1488, -6), (key1514, 6), (key1868, 6), (key1878, -6)]

def row4784 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4785 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4786 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4787 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4788 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4789 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4790 : Integer.Sparse Key := [(key1362, -6), (key1375, 6), (key1488, 6), (key1514, -6), (key1868, -6), (key1878, 6)]

def row4791 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4792 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4793 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4794 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4795 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4796 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4797 : Integer.Sparse Key := [(key351, 6), (key353, -6), (key508, -6), (key521, 6), (key628, 6), (key630, -6)]

def row4798 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4799 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4800 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4801 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4802 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4803 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4804 : Integer.Sparse Key := [(key351, -6), (key353, 6), (key508, 6), (key521, -6), (key628, -6), (key630, 6)]

def row4805 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4806 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4807 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4808 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4809 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4810 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4811 : Integer.Sparse Key := [(key1488, 6), (key1491, -6), (key1714, -6), (key1724, 6), (key1862, 6), (key1868, -6)]

def row4812 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4813 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4814 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4815 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4816 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4817 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4818 : Integer.Sparse Key := [(key1488, -6), (key1491, 6), (key1714, 6), (key1724, -6), (key1862, -6), (key1868, 6)]

def row4819 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4820 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4821 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4822 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4823 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4824 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4825 : Integer.Sparse Key := [(key291, 6), (key294, -6), (key518, -6), (key553, 6), (key631, 6), (key647, -6)]

def row4826 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4827 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4828 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4829 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4830 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4831 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4832 : Integer.Sparse Key := [(key291, -6), (key294, 6), (key518, 6), (key553, -6), (key631, -6), (key647, 6)]

def row4833 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4834 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4835 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4848 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4849 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4850 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4851 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

def row4852 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

def row4853 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4950 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4951 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4952 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4953 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4954 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4955 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4956 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4957 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4958 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4959 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4960 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4961 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4962 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4963 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4964 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4965 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4966 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4967 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4968 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4969 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4970 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4971 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4972 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4973 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4974 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4975 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4976 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4977 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4978 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4979 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4980 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4981 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4982 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4983 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4984 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4985 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4986 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4987 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4988 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4989 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

def row4990 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

def row4991 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4992 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4993 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4994 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4995 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4996 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4997 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4998 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row4999 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row5000 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row5001 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5002 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5003 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5004 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5005 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5006 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5007 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5008 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5009 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5010 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5011 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5012 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5013 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5014 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5015 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5016 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5017 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5018 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5019 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5020 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5021 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5023 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5024 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5025 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5026 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5027 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5029 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5030 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5031 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5032 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5033 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5034 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5035 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5036 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5037 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5038 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5039 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5040 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5041 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5042 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5043 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5044 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5045 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5046 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5047 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5048 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key3017, -2), (key3026, 2)]

def row5050 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

def row5051 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

def row5052 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5053 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5054 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5055 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 2), (key2835, -4), (key2885, 2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, 2)]

def row5056 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

def row5057 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

def row5058 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5059 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5060 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5061 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5062 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5063 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5064 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5065 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5066 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5067 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5068 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5069 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5070 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5071 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5072 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5073 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5074 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5075 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5076 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5077 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5078 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5079 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5080 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5081 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5082 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5083 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5084 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5085 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5086 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5087 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5088 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5089 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5090 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5091 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5092 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5093 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5094 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5095 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5096 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5097 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5098 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5112 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1159 : Sparse Master := [(Sum.inr 1159, (1 / 1))]

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

def nodeValue1220 : Sparse Master := [(Sum.inr 1220, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


