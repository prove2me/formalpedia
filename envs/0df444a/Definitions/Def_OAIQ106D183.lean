-- Prove2me | Definitions.Def_OAIQ106D183
-- name    : OAIQ106D183
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:44:31.522159+00:00
-- url     : https://prove2.me/theorems/d8a1c5f8-c09f-4afa-b915-295be4268d82
-- title:
--   Definitions bundle OAIQ106D183 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 554 declarations of OpenAI's Lean: 553 definitions and 1 theorem. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow7281`, `OAI.MUB6.Certificate.GramRows.rawRow7282`, `OAI.MUB6.Certificate.GramRows.rawRow7283`, `OAI.MUB6.Certificate.GramRows.rawRow7284`, `OAI.MUB6.Certificate.GramRows.rawRow7285`, `OAI.MUB6.Certificate.GramRows.rawRow7286`, `OAI.MUB6.Certificate.GramRows.rawRow7287`, `OAI.MUB6.Certificate.GramRows.rawRow7288`, `OAI.MUB6.Certificate.GramRows.rawRow7289`, `OAI.MUB6.Certificate.GramRows.rawRow7290`, `OAI.MUB6.Certificate.GramRows.rawRow7291`, `OAI.MUB6.Certificate.GramRows.rawRow7292`, `OAI.MUB6.Certificate.GramRows.rawRow7293`, `OAI.MUB6.Certificate.GramRows.rawRow7294`, `OAI.MUB6.Certificate.GramRows.rawRow7295`, `OAI.MUB6.Certificate.GramRows.rawRow7296`, `OAI.MUB6.Certificate.GramRows.rawRow7297`, `OAI.MUB6.Certificate.GramRows.rawRow7298`, `OAI.MUB6.Certificate.GramRows.rawRow7299`, `OAI.MUB6.Certificate.GramRows.rawRow73`, `OAI.MUB6.Certificate.GramRows.rawRow730`, `OAI.MUB6.Certificate.GramRows.rawRow7300`, `OAI.MUB6.Certificate.GramRows.rawRow7301`, `OAI.MUB6.Certificate.GramRows.rawRow7302`, `OAI.MUB6.Certificate.GramRows.rawRow7303`, `OAI.MUB6.Certificate.GramRows.rawRow7304`, `OAI.MUB6.Certificate.GramRows.rawRow7305`, `OAI.MUB6.Certificate.GramRows.rawRow7306`, `OAI.MUB6.Certificate.GramRows.rawRow7307`, `OAI.MUB6.Certificate.GramRows.rawRow7308`, `OAI.MUB6.Certificate.GramRows.rawRow7309`, `OAI.MUB6.Certificate.GramRows.rawRow731`, `OAI.MUB6.Certificate.GramRows.rawRow7310`, `OAI.MUB6.Certificate.GramRows.rawRow7311`, `OAI.MUB6.Certificate.GramRows.rawRow7312`, `OAI.MUB6.Certificate.GramRows.rawRow7313`, `OAI.MUB6.Certificate.GramRows.rawRow7314`, `OAI.MUB6.Certificate.GramRows.rawRow7315`, `OAI.MUB6.Certificate.GramRows.rawRow7316`, `OAI.MUB6.Certificate.GramRows.rawRow7317` and 513 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Certificate_Interpretation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/Interpretation.lean), [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block19.lean), [`MutuallyUnbiased_GramRows_Block20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block20.lean), [`MutuallyUnbiased_GramRows_Block21`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block21.lean), [`MutuallyUnbiased_GramRows_Block80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block80.lean), [`MutuallyUnbiased_GramRows_Block81`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block81.lean), [`MutuallyUnbiased_GramRows_Block82`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block82.lean), [`MutuallyUnbiased_GramRows_Block83`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block83.lean), [`MutuallyUnbiased_GramRows_Block84`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block84.lean), [`MutuallyUnbiased_GramRows_Block85`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block85.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090` and `OAIQ106D098` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D199`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1` and `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D098

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Integer.Sparse

variable {ι κ Ω : Type*}

@[simp] theorem eval_reindex (f : ι → κ) (v : Integer.Sparse ι) (x : κ → ℝ) :
    eval (reindex f v) x = eval v (x ∘ f) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change (p.2 : ℝ) * x (f p.1) + eval (reindex f v) x =
      (p.2 : ℝ) * x (f p.1) + eval v (x ∘ f)
    rw [ih]

end Integer.Sparse
end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow73 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1780, 2), (key1790, 1), (key1788, 1), (key1841, -1), (key1817, -1), (key1798, -2), (key1844, 1), (key1825, 1), (key1339, 1), (key1337, 1), (key1345, -2), (key1457, -1), (key1455, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1844, -1), (key1667, -1), (key1302, -1), (key1296, -1), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1780, -1), (key1559, -1), (key1466, -1), (key1447, -1), (key1798, 1), (key1596, 1), (key1296, 2), (key1337, -1), (key1316, -1), (key1391, -2), (key1772, 1), (key1546, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

def rawRow74 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1774, 2), (key1813, 1), (key1817, 1), (key1790, -1), (key1839, -1), (key1825, -2), (key1798, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1339, -2), (key1655, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1466, -1), (key1844, -1), (key1316, -1), (key1329, -1), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1397, -1), (key1774, -1), (key1596, -1), (key1667, -1), (key1447, 1), (key1825, 1), (key1316, 2), (key1296, -1), (key1337, -1), (key1546, -2), (key1391, 1), (key1772, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

def rawRow75 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1774, 2), (key1817, 1), (key1813, 1), (key1839, -1), (key1790, -1), (key1825, -2), (key1844, 1), (key1798, 1), (key1345, 1), (key1337, 1), (key1339, -2), (key1659, -1), (key1655, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1844, -1), (key1466, -1), (key1329, -1), (key1316, -1), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1774, -1), (key1397, -1), (key1667, -1), (key1596, -1), (key1825, 1), (key1447, 1), (key1316, 2), (key1337, -1), (key1296, -1), (key1546, -2), (key1772, 1), (key1391, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

def rawRow76 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1798, 2), (key1772, 1), (key1774, 1), (key1825, -1), (key1844, -1), (key1780, -2), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1466, -2), (key1337, -1), (key1339, -1), (key1667, 1), (key1844, 1), (key1345, 2), (key1659, -1), (key1841, -1), (key1391, -1), (key1397, -1), (key1447, 1), (key1466, 1), (key1296, 1), (key1302, 1), (key1596, -1), (key1798, -1), (key1329, -1), (key1345, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1424, -1), (key1455, -1), (key1296, -2), (key1573, 1), (key1788, 1), (key1316, 1), (key1337, 1), (key1546, -1), (key1772, -1)]

def rawRow77 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1798, 2), (key1774, 1), (key1772, 1), (key1844, -1), (key1825, -1), (key1780, -2), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1466, -2), (key1339, -1), (key1337, -1), (key1844, 1), (key1667, 1), (key1345, 2), (key1841, -1), (key1659, -1), (key1397, -1), (key1391, -1), (key1466, 1), (key1447, 1), (key1302, 1), (key1296, 1), (key1798, -1), (key1596, -1), (key1345, -1), (key1329, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1455, -1), (key1424, -1), (key1296, -2), (key1788, 1), (key1573, 1), (key1337, 1), (key1316, 1), (key1772, -1), (key1546, -1)]

def rawRow78 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1790, 2), (key1813, 1), (key1825, 1), (key1774, -1), (key1839, -1), (key1817, -2), (key1780, 1), (key1841, 1), (key1455, 1), (key1466, 1), (key1457, -2), (key1655, -1), (key1667, -1), (key1339, 1), (key1839, 1), (key1659, 2), (key1345, -1), (key1841, -1), (key1424, -1), (key1447, -1), (key1397, 1), (key1457, 1), (key1573, 1), (key1596, 1), (key1302, -1), (key1790, -1), (key1559, -1), (key1659, -1), (key1329, 1), (key1817, 1), (key1424, 2), (key1391, -1), (key1455, -1), (key1573, -2), (key1296, 1), (key1788, 1), (key1546, 1), (key1655, 1), (key1316, -1), (key1813, -1)]

def rawRow79 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1790, 2), (key1825, 1), (key1813, 1), (key1839, -1), (key1774, -1), (key1817, -2), (key1841, 1), (key1780, 1), (key1466, 1), (key1455, 1), (key1457, -2), (key1667, -1), (key1655, -1), (key1839, 1), (key1339, 1), (key1659, 2), (key1841, -1), (key1345, -1), (key1447, -1), (key1424, -1), (key1457, 1), (key1397, 1), (key1596, 1), (key1573, 1), (key1790, -1), (key1302, -1), (key1659, -1), (key1559, -1), (key1817, 1), (key1329, 1), (key1424, 2), (key1455, -1), (key1391, -1), (key1573, -2), (key1788, 1), (key1296, 1), (key1655, 1), (key1546, 1), (key1813, -1), (key1316, -1)]

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

def rawRow730 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1417, 2), (key1471, 2), (key1566, 6), (key1289, -2), (key1566, -2), (key1902, -2), (key1539, -2), (key1615, -2), (key1680, -2), (key1309, 2), (key1615, 2), (key1917, 2)]

def rawRow731 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1471, 2), (key1417, 2), (key1566, 6), (key1289, -2), (key1902, -2), (key1566, -2), (key1539, -2), (key1680, -2), (key1615, -2), (key1309, 2), (key1917, 2), (key1615, 2)]

def rawRow732 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1384, 2), (key1471, 2), (key1566, 6), (key1566, -2), (key1289, -2), (key1902, -2), (key1615, -2), (key1539, -2), (key1680, -2), (key1615, 2), (key1309, 2), (key1917, 2)]

def rawRow733 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1471, 2), (key1384, 2), (key1566, 6), (key1566, -2), (key1902, -2), (key1289, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, 2), (key1917, 2), (key1309, 2)]

def rawRow734 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1384, 2), (key1417, 2), (key1566, 6), (key1902, -2), (key1289, -2), (key1566, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, 2), (key1309, 2), (key1615, 2)]

def rawRow735 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1417, 2), (key1384, 2), (key1566, 6), (key1902, -2), (key1566, -2), (key1289, -2), (key1680, -2), (key1615, -2), (key1539, -2), (key1917, 2), (key1615, 2), (key1309, 2)]

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

def rawRow736 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1615, 2), (key1680, 2), (key1309, 6), (key1417, -2), (key1615, -2), (key1917, -2), (key1289, -2), (key1309, -2), (key1350, -2), (key1384, 2), (key1539, 2), (key1895, 2)]

def rawRow737 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1680, 2), (key1615, 2), (key1309, 6), (key1417, -2), (key1917, -2), (key1615, -2), (key1289, -2), (key1350, -2), (key1309, -2), (key1384, 2), (key1895, 2), (key1539, 2)]

def rawRow738 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1566, 2), (key1680, 2), (key1309, 6), (key1615, -2), (key1417, -2), (key1917, -2), (key1309, -2), (key1289, -2), (key1350, -2), (key1539, 2), (key1384, 2), (key1895, 2)]

def rawRow739 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1680, 2), (key1566, 2), (key1309, 6), (key1615, -2), (key1917, -2), (key1417, -2), (key1309, -2), (key1350, -2), (key1289, -2), (key1539, 2), (key1895, 2), (key1384, 2)]

def rawRow740 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1566, 2), (key1615, 2), (key1309, 6), (key1917, -2), (key1417, -2), (key1615, -2), (key1350, -2), (key1289, -2), (key1309, -2), (key1895, 2), (key1384, 2), (key1539, 2)]

def rawRow741 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1615, 2), (key1566, 2), (key1309, 6), (key1917, -2), (key1615, -2), (key1417, -2), (key1350, -2), (key1309, -2), (key1289, -2), (key1895, 2), (key1539, 2), (key1384, 2)]

def rawRow742 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1615, 2), (key1680, 2), (key1417, 6), (key1309, -2), (key1615, -2), (key1917, -2), (key1384, -2), (key1417, -2), (key1471, -2), (key1289, 2), (key1566, 2), (key1902, 2)]

def rawRow743 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1680, 2), (key1615, 2), (key1417, 6), (key1309, -2), (key1917, -2), (key1615, -2), (key1384, -2), (key1471, -2), (key1417, -2), (key1289, 2), (key1902, 2), (key1566, 2)]

def rawRow744 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1539, 2), (key1680, 2), (key1417, 6), (key1615, -2), (key1309, -2), (key1917, -2), (key1417, -2), (key1384, -2), (key1471, -2), (key1566, 2), (key1289, 2), (key1902, 2)]

def rawRow745 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1680, 2), (key1539, 2), (key1417, 6), (key1615, -2), (key1917, -2), (key1309, -2), (key1417, -2), (key1471, -2), (key1384, -2), (key1566, 2), (key1902, 2), (key1289, 2)]

def rawRow746 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1539, 2), (key1615, 2), (key1417, 6), (key1917, -2), (key1309, -2), (key1615, -2), (key1471, -2), (key1384, -2), (key1417, -2), (key1902, 2), (key1289, 2), (key1566, 2)]

def rawRow747 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1615, 2), (key1539, 2), (key1417, 6), (key1917, -2), (key1615, -2), (key1309, -2), (key1471, -2), (key1417, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1289, 2)]

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

def rawRow778 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1033, 1), (key1041, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1076, 1), (key1111, 2), (key1111, 2), (key1155, 2), (key1111, -1), (key1127, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1155, -1), (key1190, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1212, -1), (key1190, 1), (key1199, 1), (key1190, 1), (key1212, 1), (key1199, 1), (key1212, 1)]

def rawRow779 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 1), (key1033, 1), (key1076, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1111, 2), (key1155, 2), (key1111, 2), (key1127, -1), (key1111, -1), (key1155, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1199, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1199, 1)]

def rawRow780 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1076, 1), (key1076, 1), (key1041, 1), (key1041, 1), (key1033, 1), (key1033, 1), (key1155, 2), (key1111, 2), (key1111, 2), (key1155, -1), (key1155, -1), (key1127, -1), (key1127, -1), (key1111, -1), (key1111, -1), (key1212, -1), (key1212, -1), (key1193, -1), (key1193, -1), (key1190, -1), (key1190, -1), (key1212, 1), (key1212, 1), (key1199, 1), (key1199, 1), (key1190, 1), (key1190, 1)]

def rawRow782 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1190, 1), (key1193, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1212, 1), (key1033, 2), (key1033, 2), (key1076, 2), (key1190, -1), (key1199, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1212, -1), (key1033, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1076, -1), (key1111, 1), (key1127, 1), (key1111, 1), (key1155, 1), (key1127, 1), (key1155, 1)]

def rawRow783 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1193, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1127, 1), (key1111, 1), (key1155, 1), (key1111, 1), (key1155, 1), (key1127, 1)]

def rawRow784 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1212, 1), (key1212, 1), (key1193, 1), (key1193, 1), (key1190, 1), (key1190, 1), (key1076, 2), (key1033, 2), (key1033, 2), (key1212, -1), (key1212, -1), (key1199, -1), (key1199, -1), (key1190, -1), (key1190, -1), (key1076, -1), (key1076, -1), (key1041, -1), (key1041, -1), (key1033, -1), (key1033, -1), (key1155, 1), (key1155, 1), (key1127, 1), (key1127, 1), (key1111, 1), (key1111, 1)]

def rawRow785 : Integer.Sparse Key := [(key1006, -2), (key1193, -2), (key1193, -2), (key998, 1), (key998, 1), (key1111, 1), (key1111, 1), (key1190, 1), (key1190, 1), (key1019, 2), (key1199, 2), (key1199, 2), (key998, -1), (key998, -1), (key1033, -1), (key1033, -1), (key1190, -1), (key1190, -1), (key1019, -1), (key1019, -1), (key1127, -1), (key1127, -1), (key1199, -1), (key1199, -1), (key1006, 1), (key1006, 1), (key1041, 1), (key1041, 1), (key1193, 1), (key1193, 1)]

def rawRow786 : Integer.Sparse Key := [(key1193, -2), (key1006, -2), (key1193, -2), (key1111, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1111, 1), (key1199, 2), (key1019, 2), (key1199, 2), (key1033, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1033, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1041, 1), (key1193, 1), (key1006, 1), (key1193, 1), (key1006, 1), (key1041, 1)]

def rawRow787 : Integer.Sparse Key := [(key1193, -2), (key1193, -2), (key1006, -2), (key1190, 1), (key1111, 1), (key1190, 1), (key998, 1), (key1111, 1), (key998, 1), (key1199, 2), (key1199, 2), (key1019, 2), (key1190, -1), (key1033, -1), (key1190, -1), (key998, -1), (key1033, -1), (key998, -1), (key1199, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1019, -1), (key1193, 1), (key1041, 1), (key1193, 1), (key1006, 1), (key1041, 1), (key1006, 1)]

def rawRow789 : Integer.Sparse Key := [(key1019, -2), (key1199, -2), (key1199, -2), (key1019, 1), (key1019, 1), (key1127, 1), (key1127, 1), (key1199, 1), (key1199, 1), (key1006, 2), (key1193, 2), (key1193, 2), (key1006, -1), (key1006, -1), (key1041, -1), (key1041, -1), (key1193, -1), (key1193, -1), (key998, -1), (key998, -1), (key1111, -1), (key1111, -1), (key1190, -1), (key1190, -1), (key998, 1), (key998, 1), (key1033, 1), (key1033, 1), (key1190, 1), (key1190, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7281 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2335, 1), (key2334, -2), (key2190, 1), (key2339, 1), (key2290, 1), (key2335, 1), (key2190, 1), (key2339, 1), (key2192, -2), (key2298, -2), (key2329, 2), (key2180, -1), (key2332, -1), (key2329, 2), (key2083, -1), (key2335, -1), (key2180, -1), (key2332, -1), (key2083, -1), (key2335, -1), (key2090, 2), (key2192, 2), (key2278, -1), (key2329, -1), (key2180, 1), (key2282, 1), (key2278, -1), (key2329, -1), (key2081, 1), (key2334, 1), (key2081, 1), (key2334, 1), (key2088, -1), (key2190, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

def rawRow7282 : Integer.Sparse Key := [(key2334, -2), (key2335, 1), (key2290, 1), (key2334, -2), (key2339, 1), (key2190, 1), (key2335, 1), (key2290, 1), (key2339, 1), (key2190, 1), (key2298, -2), (key2192, -2), (key2329, 2), (key2332, -1), (key2180, -1), (key2329, 2), (key2335, -1), (key2083, -1), (key2332, -1), (key2180, -1), (key2335, -1), (key2083, -1), (key2192, 2), (key2090, 2), (key2329, -1), (key2278, -1), (key2282, 1), (key2180, 1), (key2329, -1), (key2278, -1), (key2334, 1), (key2081, 1), (key2334, 1), (key2081, 1), (key2190, -1), (key2088, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

def rawRow7283 : Integer.Sparse Key := [(key2335, -2), (key2290, 1), (key2334, 1), (key2339, -2), (key2190, 1), (key2334, 1), (key2298, 1), (key2339, 1), (key2192, 1), (key2335, 1), (key2190, -2), (key2290, -2), (key2332, 2), (key2180, -1), (key2329, -1), (key2335, 2), (key2083, -1), (key2329, -1), (key2192, -1), (key2335, -1), (key2090, -1), (key2332, -1), (key2083, 2), (key2180, 2), (key2282, -1), (key2331, -1), (key2178, 1), (key2278, 1), (key2290, -1), (key2334, -1), (key2083, 1), (key2329, 1), (key2088, 1), (key2331, 1), (key2081, -1), (key2178, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

def rawRow7284 : Integer.Sparse Key := [(key2335, -2), (key2334, 1), (key2290, 1), (key2339, -2), (key2334, 1), (key2190, 1), (key2339, 1), (key2298, 1), (key2335, 1), (key2192, 1), (key2290, -2), (key2190, -2), (key2332, 2), (key2329, -1), (key2180, -1), (key2335, 2), (key2329, -1), (key2083, -1), (key2335, -1), (key2192, -1), (key2332, -1), (key2090, -1), (key2180, 2), (key2083, 2), (key2331, -1), (key2282, -1), (key2278, 1), (key2178, 1), (key2334, -1), (key2290, -1), (key2329, 1), (key2083, 1), (key2331, 1), (key2088, 1), (key2178, -1), (key2081, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

def rawRow7285 : Integer.Sparse Key := [(key2298, -2), (key2339, 1), (key2339, 1), (key2192, -2), (key2335, 1), (key2335, 1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2334, -2), (key2334, -2), (key2192, 2), (key2335, -1), (key2335, -1), (key2090, 2), (key2332, -1), (key2332, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2190, -1), (key2190, -1), (key2334, 1), (key2334, 1), (key2088, -1), (key2088, -1), (key2282, 1), (key2282, 1), (key2180, 1), (key2180, 1), (key2329, -1), (key2329, -1), (key2081, 1), (key2081, 1), (key2278, -1), (key2278, -1)]

def rawRow7286 : Integer.Sparse Key := [(key2339, -2), (key2298, 1), (key2339, 1), (key2335, -2), (key2192, 1), (key2335, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2334, 1), (key2190, -2), (key2290, -2), (key2335, 2), (key2192, -1), (key2335, -1), (key2332, 2), (key2090, -1), (key2332, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2290, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2331, 1), (key2083, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2178, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

def rawRow7287 : Integer.Sparse Key := [(key2339, -2), (key2339, 1), (key2298, 1), (key2335, -2), (key2335, 1), (key2192, 1), (key2334, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2290, -2), (key2190, -2), (key2335, 2), (key2335, -1), (key2192, -1), (key2332, 2), (key2332, -1), (key2090, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2334, -1), (key2290, -1), (key2290, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2331, 1), (key2088, 1), (key2329, 1), (key2083, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2178, 1), (key2178, -1), (key2081, -1)]

def rawRow7288 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key828, 1), (key828, 1), (key906, -2), (key906, -2), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key918, -2), (key911, 1), (key911, 1), (key918, -2), (key952, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key957, 4)]

def rawRow7289 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key827, 1), (key828, 1), (key822, -2), (key828, -2), (key822, 1), (key827, 1), (key828, -2), (key823, 1), (key828, 1), (key910, -2), (key911, -2), (key906, 1), (key911, 1), (key906, 1), (key910, 1), (key910, 1), (key918, 1), (key910, -2), (key911, 1), (key918, 1), (key911, -2), (key953, 4), (key952, -2), (key953, -2), (key953, -2), (key957, -2), (key953, 4)]

def rawRow7290 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key828, 1), (key827, 1), (key828, -2), (key822, -2), (key827, 1), (key822, 1), (key828, -2), (key828, 1), (key823, 1), (key911, -2), (key910, -2), (key911, 1), (key906, 1), (key910, 1), (key906, 1), (key918, 1), (key910, 1), (key910, -2), (key918, 1), (key911, 1), (key911, -2), (key953, 4), (key953, -2), (key952, -2), (key957, -2), (key953, -2), (key953, 4)]

def rawRow7291 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key822, 1), (key823, 1), (key822, -2), (key828, -2), (key823, 1), (key828, 1), (key822, -2), (key822, 1), (key827, 1), (key910, -2), (key911, -2), (key910, 1), (key918, 1), (key911, 1), (key918, 1), (key906, 1), (key911, 1), (key911, -2), (key906, 1), (key910, 1), (key910, -2), (key953, 4), (key953, -2), (key957, -2), (key952, -2), (key953, -2), (key953, 4)]

def rawRow7292 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key823, 1), (key822, 1), (key828, -2), (key822, -2), (key828, 1), (key823, 1), (key822, -2), (key827, 1), (key822, 1), (key911, -2), (key910, -2), (key918, 1), (key910, 1), (key918, 1), (key911, 1), (key911, 1), (key906, 1), (key911, -2), (key910, 1), (key906, 1), (key910, -2), (key953, 4), (key957, -2), (key953, -2), (key953, -2), (key952, -2), (key953, 4)]

def rawRow7293 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key822, 1), (key822, 1), (key918, -2), (key918, -2), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key906, -2), (key910, 1), (key910, 1), (key906, -2), (key957, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key952, 4)]

def rawRow7294 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key906, 1), (key906, 1), (key910, -2), (key910, -2), (key911, 1), (key911, 1), (key952, -2), (key953, 1), (key953, 1), (key822, -2), (key822, -2), (key827, 1), (key827, 1), (key828, 1), (key828, 1), (key910, 1), (key910, 1), (key918, -2), (key953, 1), (key953, 1), (key957, -2), (key823, 4), (key828, -2), (key828, -2), (key911, -2), (key911, -2), (key918, 4)]

def rawRow7295 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key910, 1), (key911, 1), (key906, -2), (key911, -2), (key906, 1), (key910, 1), (key953, -2), (key952, 1), (key953, 1), (key827, -2), (key828, -2), (key822, 1), (key828, 1), (key822, 1), (key827, 1), (key910, 1), (key918, 1), (key910, -2), (key953, 1), (key957, 1), (key953, -2), (key828, 4), (key823, -2), (key828, -2), (key911, -2), (key918, -2), (key911, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7296 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key911, 1), (key910, 1), (key911, -2), (key906, -2), (key910, 1), (key906, 1), (key953, -2), (key953, 1), (key952, 1), (key828, -2), (key827, -2), (key828, 1), (key822, 1), (key827, 1), (key822, 1), (key918, 1), (key910, 1), (key910, -2), (key957, 1), (key953, 1), (key953, -2), (key828, 4), (key828, -2), (key823, -2), (key918, -2), (key911, -2), (key911, 4)]

def rawRow7297 : Integer.Sparse Key := [(key906, 1), (key906, 1), (key952, -2), (key822, 1), (key822, 1), (key910, -2), (key910, -2), (key953, 1), (key953, 1), (key823, -2), (key911, 1), (key911, 1), (key822, -2), (key822, -2), (key910, 1), (key910, 1), (key953, 1), (key953, 1), (key827, 1), (key827, 1), (key957, -2), (key828, 1), (key828, 1), (key918, -2), (key823, 4), (key911, -2), (key911, -2), (key828, -2), (key828, -2), (key918, 4)]

def rawRow7298 : Integer.Sparse Key := [(key906, 1), (key952, 1), (key906, -2), (key910, 1), (key953, 1), (key822, -2), (key953, -2), (key822, 1), (key910, 1), (key911, -2), (key823, 1), (key911, 1), (key910, -2), (key953, -2), (key822, 1), (key953, 1), (key822, 1), (key910, 1), (key827, 1), (key957, 1), (key827, -2), (key828, 1), (key918, 1), (key828, -2), (key911, 4), (key823, -2), (key911, -2), (key828, -2), (key918, -2), (key828, 4)]

def rawRow7299 : Integer.Sparse Key := [(key952, 1), (key906, 1), (key906, -2), (key953, 1), (key910, 1), (key953, -2), (key822, -2), (key910, 1), (key822, 1), (key911, -2), (key911, 1), (key823, 1), (key953, -2), (key910, -2), (key953, 1), (key822, 1), (key910, 1), (key822, 1), (key957, 1), (key827, 1), (key827, -2), (key918, 1), (key828, 1), (key828, -2), (key911, 4), (key911, -2), (key823, -2), (key918, -2), (key828, -2), (key828, 4)]

def rawRow7300 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key822, 1), (key823, 1), (key906, -2), (key911, -2), (key952, 1), (key953, 1), (key822, -2), (key906, 1), (key910, 1), (key827, -2), (key828, -2), (key910, 1), (key918, 1), (key953, 1), (key957, 1), (key822, 1), (key828, 1), (key953, -2), (key822, 1), (key827, 1), (key910, -2), (key828, 4), (key911, -2), (key918, -2), (key823, -2), (key828, -2), (key911, 4)]

def rawRow7301 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key823, 1), (key822, 1), (key911, -2), (key906, -2), (key953, 1), (key952, 1), (key822, -2), (key910, 1), (key906, 1), (key828, -2), (key827, -2), (key918, 1), (key910, 1), (key957, 1), (key953, 1), (key828, 1), (key822, 1), (key953, -2), (key827, 1), (key822, 1), (key910, -2), (key828, 4), (key918, -2), (key911, -2), (key828, -2), (key823, -2), (key911, 4)]

def rawRow7302 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key906, 1), (key952, 1), (key822, -2), (key953, -2), (key823, 1), (key911, 1), (key906, -2), (key822, 1), (key910, 1), (key910, -2), (key953, -2), (key827, 1), (key957, 1), (key828, 1), (key918, 1), (key822, 1), (key953, 1), (key828, -2), (key822, 1), (key910, 1), (key827, -2), (key911, 4), (key828, -2), (key918, -2), (key823, -2), (key911, -2), (key828, 4)]

def rawRow7303 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key952, 1), (key906, 1), (key953, -2), (key822, -2), (key911, 1), (key823, 1), (key906, -2), (key910, 1), (key822, 1), (key953, -2), (key910, -2), (key957, 1), (key827, 1), (key918, 1), (key828, 1), (key953, 1), (key822, 1), (key828, -2), (key910, 1), (key822, 1), (key827, -2), (key911, 4), (key918, -2), (key828, -2), (key911, -2), (key823, -2), (key828, 4)]

def rawRow7304 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key911, 1), (key953, 1), (key823, -2), (key952, -2), (key822, 1), (key906, 1), (key910, -2), (key822, 1), (key906, 1), (key918, -2), (key957, -2), (key828, 1), (key953, 1), (key827, 1), (key910, 1), (key828, 1), (key953, 1), (key822, -2), (key827, 1), (key910, 1), (key822, -2), (key918, 4), (key828, -2), (key911, -2), (key828, -2), (key911, -2), (key823, 4)]

def rawRow7305 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key953, 1), (key911, 1), (key952, -2), (key823, -2), (key906, 1), (key822, 1), (key910, -2), (key906, 1), (key822, 1), (key957, -2), (key918, -2), (key953, 1), (key828, 1), (key910, 1), (key827, 1), (key953, 1), (key828, 1), (key822, -2), (key910, 1), (key827, 1), (key822, -2), (key918, 4), (key911, -2), (key828, -2), (key911, -2), (key828, -2), (key823, 4)]

def rawRow7306 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key910, 1), (key911, 1), (key910, -2), (key918, -2), (key911, 1), (key918, 1), (key953, -2), (key953, 1), (key957, 1), (key822, -2), (key823, -2), (key822, 1), (key828, 1), (key823, 1), (key828, 1), (key906, 1), (key911, 1), (key911, -2), (key952, 1), (key953, 1), (key953, -2), (key822, 4), (key822, -2), (key827, -2), (key906, -2), (key910, -2), (key910, 4)]

def rawRow7307 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key911, 1), (key910, 1), (key918, -2), (key910, -2), (key918, 1), (key911, 1), (key953, -2), (key957, 1), (key953, 1), (key823, -2), (key822, -2), (key828, 1), (key822, 1), (key828, 1), (key823, 1), (key911, 1), (key906, 1), (key911, -2), (key953, 1), (key952, 1), (key953, -2), (key822, 4), (key827, -2), (key822, -2), (key910, -2), (key906, -2), (key910, 4)]

def rawRow7308 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key918, 1), (key918, 1), (key911, -2), (key911, -2), (key910, 1), (key910, 1), (key957, -2), (key953, 1), (key953, 1), (key828, -2), (key828, -2), (key823, 1), (key823, 1), (key822, 1), (key822, 1), (key911, 1), (key911, 1), (key906, -2), (key953, 1), (key953, 1), (key952, -2), (key827, 4), (key822, -2), (key822, -2), (key910, -2), (key910, -2), (key906, 4)]

def rawRow7309 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key827, 1), (key828, 1), (key910, -2), (key918, -2), (key953, 1), (key957, 1), (key828, -2), (key911, 1), (key918, 1), (key822, -2), (key823, -2), (key906, 1), (key911, 1), (key952, 1), (key953, 1), (key822, 1), (key828, 1), (key953, -2), (key823, 1), (key828, 1), (key911, -2), (key822, 4), (key906, -2), (key910, -2), (key822, -2), (key827, -2), (key910, 4)]

def rawRow7310 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key828, 1), (key827, 1), (key918, -2), (key910, -2), (key957, 1), (key953, 1), (key828, -2), (key918, 1), (key911, 1), (key823, -2), (key822, -2), (key911, 1), (key906, 1), (key953, 1), (key952, 1), (key828, 1), (key822, 1), (key953, -2), (key828, 1), (key823, 1), (key911, -2), (key822, 4), (key910, -2), (key906, -2), (key827, -2), (key822, -2), (key910, 4)]

def rawRow7311 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key910, 1), (key953, 1), (key827, -2), (key957, -2), (key828, 1), (key918, 1), (key911, -2), (key828, 1), (key918, 1), (key906, -2), (key952, -2), (key822, 1), (key953, 1), (key823, 1), (key911, 1), (key822, 1), (key953, 1), (key828, -2), (key823, 1), (key911, 1), (key828, -2), (key906, 4), (key822, -2), (key910, -2), (key822, -2), (key910, -2), (key827, 4)]

def rawRow7312 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key953, 1), (key910, 1), (key957, -2), (key827, -2), (key918, 1), (key828, 1), (key911, -2), (key918, 1), (key828, 1), (key952, -2), (key906, -2), (key953, 1), (key822, 1), (key911, 1), (key823, 1), (key953, 1), (key822, 1), (key828, -2), (key911, 1), (key823, 1), (key828, -2), (key906, 4), (key910, -2), (key822, -2), (key910, -2), (key822, -2), (key827, 4)]

def rawRow7313 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key918, 1), (key957, 1), (key828, -2), (key953, -2), (key827, 1), (key910, 1), (key918, -2), (key828, 1), (key911, 1), (key911, -2), (key953, -2), (key823, 1), (key952, 1), (key822, 1), (key906, 1), (key828, 1), (key953, 1), (key822, -2), (key828, 1), (key911, 1), (key823, -2), (key910, 4), (key822, -2), (key906, -2), (key827, -2), (key910, -2), (key822, 4)]

def rawRow7314 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key957, 1), (key918, 1), (key953, -2), (key828, -2), (key910, 1), (key827, 1), (key918, -2), (key911, 1), (key828, 1), (key953, -2), (key911, -2), (key952, 1), (key823, 1), (key906, 1), (key822, 1), (key953, 1), (key828, 1), (key822, -2), (key911, 1), (key828, 1), (key823, -2), (key910, 4), (key906, -2), (key822, -2), (key910, -2), (key827, -2), (key822, 4)]

def rawRow7315 : Integer.Sparse Key := [(key918, 1), (key918, 1), (key957, -2), (key828, 1), (key828, 1), (key911, -2), (key911, -2), (key953, 1), (key953, 1), (key827, -2), (key910, 1), (key910, 1), (key828, -2), (key828, -2), (key911, 1), (key911, 1), (key953, 1), (key953, 1), (key823, 1), (key823, 1), (key952, -2), (key822, 1), (key822, 1), (key906, -2), (key827, 4), (key910, -2), (key910, -2), (key822, -2), (key822, -2), (key906, 4)]

def rawRow7316 : Integer.Sparse Key := [(key918, 1), (key957, 1), (key918, -2), (key911, 1), (key953, 1), (key828, -2), (key953, -2), (key828, 1), (key911, 1), (key910, -2), (key827, 1), (key910, 1), (key911, -2), (key953, -2), (key828, 1), (key953, 1), (key828, 1), (key911, 1), (key823, 1), (key952, 1), (key823, -2), (key822, 1), (key906, 1), (key822, -2), (key910, 4), (key827, -2), (key910, -2), (key822, -2), (key906, -2), (key822, 4)]

def rawRow7317 : Integer.Sparse Key := [(key957, 1), (key918, 1), (key918, -2), (key953, 1), (key911, 1), (key953, -2), (key828, -2), (key911, 1), (key828, 1), (key910, -2), (key910, 1), (key827, 1), (key953, -2), (key911, -2), (key953, 1), (key828, 1), (key911, 1), (key828, 1), (key952, 1), (key823, 1), (key823, -2), (key906, 1), (key822, 1), (key822, -2), (key910, 4), (key910, -2), (key827, -2), (key906, -2), (key822, -2), (key822, 4)]

def rawRow7318 : Integer.Sparse Key := [(key781, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key786, -4), (key806, 2), (key809, -1), (key809, -1), (key806, 2), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key816, 2), (key816, 2), (key822, -1), (key822, -1), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key828, -1), (key828, -1)]

def rawRow7319 : Integer.Sparse Key := [(key784, -4), (key781, 2), (key784, 2), (key784, 2), (key786, 2), (key784, -4), (key809, 2), (key806, -1), (key809, -1), (key814, 2), (key806, -1), (key814, -1), (key814, -1), (key816, -1), (key809, -1), (key816, -1), (key809, 2), (key814, 2), (key822, -1), (key823, -1), (key822, 2), (key827, -1), (key828, -1), (key822, 2), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key823, -1), (key828, -1)]

def rawRow7320 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key781, 2), (key786, 2), (key784, 2), (key784, -4), (key809, 2), (key809, -1), (key806, -1), (key814, 2), (key814, -1), (key806, -1), (key816, -1), (key814, -1), (key816, -1), (key809, -1), (key814, 2), (key809, 2), (key823, -1), (key822, -1), (key822, 2), (key828, -1), (key827, -1), (key828, 2), (key822, 2), (key827, -1), (key822, -1), (key828, 2), (key828, -1), (key823, -1)]

def rawRow7321 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key786, 2), (key781, 2), (key784, 2), (key784, -4), (key814, 2), (key814, -1), (key816, -1), (key809, 2), (key809, -1), (key816, -1), (key806, -1), (key809, -1), (key806, -1), (key814, -1), (key809, 2), (key814, 2), (key827, -1), (key828, -1), (key828, 2), (key822, -1), (key823, -1), (key822, 2), (key828, 2), (key823, -1), (key828, -1), (key822, 2), (key822, -1), (key827, -1)]

def rawRow7322 : Integer.Sparse Key := [(key784, -4), (key786, 2), (key784, 2), (key784, 2), (key781, 2), (key784, -4), (key814, 2), (key816, -1), (key814, -1), (key809, 2), (key816, -1), (key809, -1), (key809, -1), (key806, -1), (key814, -1), (key806, -1), (key814, 2), (key809, 2), (key828, -1), (key827, -1), (key828, 2), (key823, -1), (key822, -1), (key828, 2), (key822, 2), (key828, -1), (key823, -1), (key822, 2), (key827, -1), (key822, -1)]

def rawRow7323 : Integer.Sparse Key := [(key786, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key781, -4), (key816, 2), (key814, -1), (key814, -1), (key816, 2), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key806, 2), (key806, 2), (key828, -1), (key828, -1), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key822, -1), (key822, -1)]

def rawRow7324 : Integer.Sparse Key := [(key806, -4), (key809, 2), (key809, 2), (key814, 2), (key814, 2), (key816, -4), (key781, 2), (key784, -1), (key784, -1), (key806, 2), (key814, -1), (key814, -1), (key822, -1), (key822, -1), (key827, -1), (key827, -1), (key828, 2), (key828, 2), (key784, -1), (key784, -1), (key786, 2), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key816, -1), (key816, -1), (key823, 2), (key828, -1), (key828, -1)]

def rawRow7325 : Integer.Sparse Key := [(key809, -4), (key806, 2), (key809, 2), (key814, 2), (key816, 2), (key814, -4), (key784, 2), (key781, -1), (key784, -1), (key814, 2), (key806, -1), (key814, -1), (key827, -1), (key828, -1), (key822, -1), (key828, -1), (key822, 2), (key827, 2), (key784, -1), (key786, -1), (key784, 2), (key814, -1), (key816, -1), (key809, 2), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key823, -1), (key828, -1)]

def rawRow7326 : Integer.Sparse Key := [(key809, -4), (key809, 2), (key806, 2), (key816, 2), (key814, 2), (key814, -4), (key784, 2), (key784, -1), (key781, -1), (key814, 2), (key814, -1), (key806, -1), (key828, -1), (key827, -1), (key828, -1), (key822, -1), (key827, 2), (key822, 2), (key786, -1), (key784, -1), (key784, 2), (key816, -1), (key814, -1), (key816, 2), (key809, 2), (key814, -1), (key809, -1), (key828, 2), (key828, -1), (key823, -1)]

def rawRow7327 : Integer.Sparse Key := [(key806, -4), (key814, 2), (key814, 2), (key809, 2), (key809, 2), (key816, -4), (key806, 2), (key814, -1), (key814, -1), (key781, 2), (key827, -1), (key827, -1), (key784, -1), (key784, -1), (key814, -1), (key814, -1), (key828, 2), (key828, 2), (key809, -1), (key809, -1), (key823, 2), (key784, -1), (key784, -1), (key814, 2), (key814, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1)]

def rawRow7328 : Integer.Sparse Key := [(key814, -4), (key806, 2), (key814, 2), (key809, 2), (key816, 2), (key809, -4), (key814, 2), (key806, -1), (key814, -1), (key827, 2), (key781, -1), (key827, -1), (key814, -1), (key828, -1), (key784, -1), (key828, -1), (key784, 2), (key814, 2), (key809, -1), (key823, -1), (key809, 2), (key814, -1), (key828, -1), (key784, 2), (key828, 2), (key784, -1), (key814, -1), (key816, 2), (key786, -1), (key816, -1)]

def rawRow7329 : Integer.Sparse Key := [(key814, -4), (key814, 2), (key806, 2), (key816, 2), (key809, 2), (key809, -4), (key814, 2), (key814, -1), (key806, -1), (key827, 2), (key827, -1), (key781, -1), (key828, -1), (key814, -1), (key828, -1), (key784, -1), (key814, 2), (key784, 2), (key823, -1), (key809, -1), (key809, 2), (key828, -1), (key814, -1), (key828, 2), (key784, 2), (key814, -1), (key784, -1), (key816, 2), (key816, -1), (key786, -1)]

def rawRow7330 : Integer.Sparse Key := [(key809, -4), (key814, 2), (key816, 2), (key806, 2), (key809, 2), (key814, -4), (key822, 2), (key827, -1), (key828, -1), (key784, 2), (key814, -1), (key828, -1), (key781, -1), (key784, -1), (key806, -1), (key814, -1), (key822, 2), (key827, 2), (key814, -1), (key816, -1), (key828, 2), (key784, -1), (key786, -1), (key809, 2), (key816, 2), (key823, -1), (key828, -1), (key784, 2), (key809, -1), (key814, -1)]

def rawRow7331 : Integer.Sparse Key := [(key809, -4), (key816, 2), (key814, 2), (key809, 2), (key806, 2), (key814, -4), (key822, 2), (key828, -1), (key827, -1), (key784, 2), (key828, -1), (key814, -1), (key784, -1), (key781, -1), (key814, -1), (key806, -1), (key827, 2), (key822, 2), (key816, -1), (key814, -1), (key828, 2), (key786, -1), (key784, -1), (key816, 2), (key809, 2), (key828, -1), (key823, -1), (key784, 2), (key814, -1), (key809, -1)]

def rawRow7332 : Integer.Sparse Key := [(key814, -4), (key809, 2), (key816, 2), (key806, 2), (key814, 2), (key809, -4), (key827, 2), (key822, -1), (key828, -1), (key814, 2), (key784, -1), (key828, -1), (key806, -1), (key814, -1), (key781, -1), (key827, -1), (key784, 2), (key814, 2), (key814, -1), (key828, -1), (key816, 2), (key809, -1), (key823, -1), (key784, 2), (key828, 2), (key786, -1), (key816, -1), (key809, 2), (key784, -1), (key814, -1)]

def rawRow7333 : Integer.Sparse Key := [(key814, -4), (key816, 2), (key809, 2), (key814, 2), (key806, 2), (key809, -4), (key827, 2), (key828, -1), (key822, -1), (key814, 2), (key828, -1), (key784, -1), (key814, -1), (key806, -1), (key827, -1), (key781, -1), (key814, 2), (key784, 2), (key828, -1), (key814, -1), (key816, 2), (key823, -1), (key809, -1), (key828, 2), (key784, 2), (key816, -1), (key786, -1), (key809, 2), (key814, -1), (key784, -1)]

def rawRow7334 : Integer.Sparse Key := [(key816, -4), (key809, 2), (key814, 2), (key809, 2), (key814, 2), (key806, -4), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key784, -1), (key814, -1), (key822, -1), (key827, -1), (key784, -1), (key814, -1), (key781, 2), (key806, 2), (key816, -1), (key828, -1), (key814, 2), (key816, -1), (key828, -1), (key786, 2), (key823, 2), (key784, -1), (key809, -1), (key814, 2), (key784, -1), (key809, -1)]

def rawRow7335 : Integer.Sparse Key := [(key816, -4), (key814, 2), (key809, 2), (key814, 2), (key809, 2), (key806, -4), (key828, 2), (key827, -1), (key822, -1), (key828, 2), (key814, -1), (key784, -1), (key827, -1), (key822, -1), (key814, -1), (key784, -1), (key806, 2), (key781, 2), (key828, -1), (key816, -1), (key814, 2), (key828, -1), (key816, -1), (key823, 2), (key786, 2), (key809, -1), (key784, -1), (key814, 2), (key809, -1), (key784, -1)]

def rawRow7336 : Integer.Sparse Key := [(key822, -4), (key822, 2), (key823, 2), (key827, 2), (key828, 2), (key828, -4), (key784, 2), (key784, -1), (key786, -1), (key809, 2), (key809, -1), (key823, -1), (key814, -1), (key816, -1), (key814, -1), (key828, -1), (key816, 2), (key828, 2), (key781, -1), (key784, -1), (key784, 2), (key806, -1), (key809, -1), (key806, 2), (key814, 2), (key809, -1), (key814, -1), (key822, 2), (key822, -1), (key827, -1)]

def rawRow7337 : Integer.Sparse Key := [(key822, -4), (key823, 2), (key822, 2), (key828, 2), (key827, 2), (key828, -4), (key784, 2), (key786, -1), (key784, -1), (key809, 2), (key823, -1), (key809, -1), (key816, -1), (key814, -1), (key828, -1), (key814, -1), (key828, 2), (key816, 2), (key784, -1), (key781, -1), (key784, 2), (key809, -1), (key806, -1), (key814, 2), (key806, 2), (key814, -1), (key809, -1), (key822, 2), (key827, -1), (key822, -1)]

def rawRow7338 : Integer.Sparse Key := [(key823, -4), (key822, 2), (key822, 2), (key828, 2), (key828, 2), (key827, -4), (key786, 2), (key784, -1), (key784, -1), (key823, 2), (key809, -1), (key809, -1), (key828, -1), (key828, -1), (key816, -1), (key816, -1), (key814, 2), (key814, 2), (key784, -1), (key784, -1), (key781, 2), (key814, -1), (key814, -1), (key809, 2), (key809, 2), (key806, -1), (key806, -1), (key827, 2), (key822, -1), (key822, -1)]

def rawRow7339 : Integer.Sparse Key := [(key822, -4), (key827, 2), (key828, 2), (key822, 2), (key823, 2), (key828, -4), (key809, 2), (key814, -1), (key816, -1), (key784, 2), (key814, -1), (key828, -1), (key784, -1), (key786, -1), (key809, -1), (key823, -1), (key816, 2), (key828, 2), (key806, -1), (key809, -1), (key814, 2), (key781, -1), (key784, -1), (key806, 2), (key814, 2), (key822, -1), (key827, -1), (key784, 2), (key809, -1), (key814, -1)]

def rawRow7340 : Integer.Sparse Key := [(key822, -4), (key828, 2), (key827, 2), (key823, 2), (key822, 2), (key828, -4), (key809, 2), (key816, -1), (key814, -1), (key784, 2), (key828, -1), (key814, -1), (key786, -1), (key784, -1), (key823, -1), (key809, -1), (key828, 2), (key816, 2), (key809, -1), (key806, -1), (key814, 2), (key784, -1), (key781, -1), (key814, 2), (key806, 2), (key827, -1), (key822, -1), (key784, 2), (key814, -1), (key809, -1)]

def rawRow7341 : Integer.Sparse Key := [(key827, -4), (key822, 2), (key828, 2), (key822, 2), (key828, 2), (key823, -4), (key814, 2), (key809, -1), (key816, -1), (key814, 2), (key784, -1), (key828, -1), (key809, -1), (key816, -1), (key784, -1), (key828, -1), (key786, 2), (key823, 2), (key806, -1), (key814, -1), (key809, 2), (key806, -1), (key814, -1), (key781, 2), (key827, 2), (key784, -1), (key814, -1), (key809, 2), (key784, -1), (key814, -1)]

def rawRow7342 : Integer.Sparse Key := [(key827, -4), (key828, 2), (key822, 2), (key828, 2), (key822, 2), (key823, -4), (key814, 2), (key816, -1), (key809, -1), (key814, 2), (key828, -1), (key784, -1), (key816, -1), (key809, -1), (key828, -1), (key784, -1), (key823, 2), (key786, 2), (key814, -1), (key806, -1), (key809, 2), (key814, -1), (key806, -1), (key827, 2), (key781, 2), (key814, -1), (key784, -1), (key809, 2), (key814, -1), (key784, -1)]

def rawRow7343 : Integer.Sparse Key := [(key828, -4), (key822, 2), (key827, 2), (key823, 2), (key828, 2), (key822, -4), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key784, -1), (key814, -1), (key823, -1), (key828, -1), (key786, -1), (key816, -1), (key784, 2), (key809, 2), (key809, -1), (key814, -1), (key806, 2), (key822, -1), (key827, -1), (key784, 2), (key814, 2), (key781, -1), (key806, -1), (key814, 2), (key784, -1), (key809, -1)]

def rawRow7344 : Integer.Sparse Key := [(key828, -4), (key827, 2), (key822, 2), (key828, 2), (key823, 2), (key822, -4), (key816, 2), (key814, -1), (key809, -1), (key828, 2), (key814, -1), (key784, -1), (key828, -1), (key823, -1), (key816, -1), (key786, -1), (key809, 2), (key784, 2), (key814, -1), (key809, -1), (key806, 2), (key827, -1), (key822, -1), (key814, 2), (key784, 2), (key806, -1), (key781, -1), (key814, 2), (key809, -1), (key784, -1)]

def rawRow7345 : Integer.Sparse Key := [(key823, -4), (key828, 2), (key828, 2), (key822, 2), (key822, 2), (key827, -4), (key823, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1), (key784, -1), (key784, -1), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key822, -1), (key822, -1), (key827, 2), (key784, -1), (key784, -1), (key809, 2), (key809, 2), (key814, -1), (key814, -1), (key781, 2), (key806, -1), (key806, -1)]

def rawRow7346 : Integer.Sparse Key := [(key828, -4), (key823, 2), (key828, 2), (key822, 2), (key827, 2), (key822, -4), (key828, 2), (key823, -1), (key828, -1), (key816, 2), (key786, -1), (key816, -1), (key809, -1), (key814, -1), (key784, -1), (key814, -1), (key784, 2), (key809, 2), (key822, -1), (key827, -1), (key822, 2), (key809, -1), (key814, -1), (key784, 2), (key814, 2), (key784, -1), (key809, -1), (key806, 2), (key781, -1), (key806, -1)]

def rawRow7347 : Integer.Sparse Key := [(key828, -4), (key828, 2), (key823, 2), (key827, 2), (key822, 2), (key822, -4), (key828, 2), (key828, -1), (key823, -1), (key816, 2), (key816, -1), (key786, -1), (key814, -1), (key809, -1), (key814, -1), (key784, -1), (key809, 2), (key784, 2), (key827, -1), (key822, -1), (key822, 2), (key814, -1), (key809, -1), (key814, 2), (key784, 2), (key809, -1), (key784, -1), (key806, 2), (key806, -1), (key781, -1)]

def rawRow7348 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2532, 2), (key2532, 2), (key2562, 2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

def rawRow7349 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

def rawRow7350 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

def rawRow7351 : Integer.Sparse Key := [(key2457, 2), (key2521, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2562, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2564, 2), (key2564, 2), (key2460, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2525, -2)]

def rawRow7352 : Integer.Sparse Key := [(key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2362, 2), (key2562, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2460, -2), (key2533, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2367, -2), (key2525, -2)]

def rawRow7353 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2562, 2), (key2362, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2533, -2), (key2460, -2), (key2460, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2525, -2), (key2525, -2), (key2367, -2)]

def rawRow7354 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2362, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

def rawRow7355 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2532, 2), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -2), (key2365, -2), (key2525, -2), (key2460, -2), (key2564, -2), (key2533, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

def rawRow7356 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2457, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

def rawRow7357 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2362, 2), (key2521, 2), (key2365, 2), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2525, -2), (key2367, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

def rawRow7358 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2362, 2), (key2457, 2), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

def rawRow7359 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2562, 2), (key2532, 2), (key2521, 2), (key2365, 2), (key2457, 2), (key2362, 2), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2533, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

def rawRow7360 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2460, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2564, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

def rawRow7361 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2533, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

def rawRow7362 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2460, 2), (key2564, 2), (key2564, 2), (key2525, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

def rawRow7363 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2533, 2), (key2525, 2), (key2564, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

def rawRow7364 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2367, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2564, 2), (key2525, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

def rawRow7365 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2365, 2), (key2564, 2), (key2367, 2), (key2533, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

def rawRow7366 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2525, 2), (key2460, 2), (key2564, 2), (key2365, 2), (key2533, 2), (key2367, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

def rawRow7367 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2533, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2365, 2), (key2460, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

def rawRow7368 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2367, 2), (key2460, 2), (key2365, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

def rawRow7369 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2525, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2457, -2)]

def rawRow7370 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2525, 2), (key2367, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2362, -2), (key2457, -2)]

def rawRow7371 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2525, 2), (key2367, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2365, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2457, -2), (key2457, -2), (key2362, -2)]

def rawRow7372 : Integer.Sparse Key := [(key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

def rawRow7373 : Integer.Sparse Key := [(key974, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key974, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

def rawRow7374 : Integer.Sparse Key := [(key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1178, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2)]

def rawRow7375 : Integer.Sparse Key := [(key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1178, 2), (key974, 2), (key1088, 2), (key1088, -2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2), (key1088, -2)]

def rawRow7376 : Integer.Sparse Key := [(key1178, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1088, 2), (key974, 2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1088, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2)]

def rawRow7382 : Integer.Sparse Key := [(key1090, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1169, 2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

def rawRow7383 : Integer.Sparse Key := [(key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1183, -2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

def rawRow7384 : Integer.Sparse Key := [(key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

def rawRow7385 : Integer.Sparse Key := [(key1169, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1180, -2)]

def rawRow7386 : Integer.Sparse Key := [(key976, 2), (key976, 2), (key984, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1180, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key1220, 2), (key976, -2), (key984, -2), (key984, -2), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

def rawRow7387 : Integer.Sparse Key := [(key976, 2), (key984, 2), (key976, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key984, -2), (key976, -2), (key984, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

def rawRow7388 : Integer.Sparse Key := [(key984, 2), (key976, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1220, 2), (key1220, 2), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, 2), (key984, -2), (key984, -2), (key976, -2), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

def rawRow7389 : Integer.Sparse Key := [(key1090, 2), (key1180, 2), (key1183, 2), (key976, 2), (key1180, 2), (key1220, 2), (key976, 2), (key984, 2), (key1090, 2), (key1169, 2), (key1183, 2), (key1220, 2), (key1090, -2), (key1098, -2), (key1183, -2), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key984, -2), (key1098, -2), (key1169, -2)]

def rawRow7390 : Integer.Sparse Key := [(key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1180, 2), (key984, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1220, 2), (key1183, 2), (key1098, -2), (key1090, -2), (key1183, -2), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, -2), (key1169, -2), (key1098, -2)]

def rawRow7391 : Integer.Sparse Key := [(key1180, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1090, 2), (key1183, 2), (key976, 2), (key1220, 2), (key984, 2), (key1169, 2), (key1090, -2), (key1183, -2), (key1098, -2), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1098, -2), (key984, -2), (key1169, -2)]

def rawRow7392 : Integer.Sparse Key := [(key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1169, 2), (key984, 2), (key1183, -2), (key1090, -2), (key1098, -2), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1098, -2), (key1169, -2), (key984, -2)]

def rawRow7393 : Integer.Sparse Key := [(key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1180, 2), (key1169, 2), (key1220, 2), (key984, 2), (key1183, 2), (key976, 2), (key1090, 2), (key1098, -2), (key1183, -2), (key1090, -2), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, -2), (key984, -2), (key1098, -2)]

def rawRow7394 : Integer.Sparse Key := [(key1183, 2), (key1180, 2), (key1090, 2), (key1220, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key1090, -2), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1169, -2), (key1098, -2), (key984, -2)]

def rawRow7395 : Integer.Sparse Key := [(key1169, 2), (key1220, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1183, 2), (key976, 2), (key976, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow7396 : Integer.Sparse Key := [(key1220, 2), (key1169, 2), (key1220, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1180, 2), (key976, 2), (key1090, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow7397 : Integer.Sparse Key := [(key1220, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1180, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1090, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow7398 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key86, 6), (key147, 6)]

def rawRow7399 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key147, 6), (key86, 6)]

def rawRow7400 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key147, 6), (key86, 6), (key86, 6)]

def rawRow7401 : Integer.Sparse Key := [(key3, -24), (key147, 6), (key86, 6), (key86, 6), (key86, 6)]

def rawRow7402 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key86, 6), (key147, 6)]

def rawRow7403 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key147, 6), (key86, 6)]

def rawRow7404 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key147, 6), (key86, 6), (key86, 6)]

def rawRow7405 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key86, 6), (key147, 6)]

def rawRow7406 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key147, 6), (key86, 6)]

def rawRow7407 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key3, 6), (key147, 6)]

def rawRow7408 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key147, 6), (key3, 6)]

def rawRow7409 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key3, 6), (key86, 6)]

def rawRow7410 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key86, 6), (key3, 6)]

def rawRow7411 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key3, 6), (key86, 6), (key86, 6)]

def rawRow7412 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key3, 6), (key86, 6)]

def rawRow7413 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key86, 6), (key3, 6)]

def rawRow7414 : Integer.Sparse Key := [(key1, -6), (key7, -6), (key7, -6), (key7, -6), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2)]

def rawRow7415 : Integer.Sparse Key := [(key7, -6), (key1, -6), (key7, -6), (key7, -6), (key90, 2), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key90, 2)]

def rawRow7416 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key1, -6), (key7, -6), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2)]

def rawRow7417 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key7, -6), (key1, -6), (key151, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key84, 2)]

def rawRow7418 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key90, -6), (key151, -6), (key1, 2), (key7, 2), (key7, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key193, 2), (key193, 2), (key202, 2)]

def rawRow7419 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key90, -6), (key151, -6), (key7, 2), (key1, 2), (key7, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key193, 2), (key202, 2), (key193, 2)]

def rawRow7420 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key84, -6), (key151, -6), (key7, 2), (key7, 2), (key1, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key202, 2), (key193, 2), (key193, 2)]

def rawRow7421 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key151, -6), (key90, -6), (key84, 2), (key90, 2), (key151, 2), (key1, 2), (key7, 2), (key84, 2), (key151, 2), (key193, 2), (key202, 2), (key7, 2), (key90, 2), (key151, 2)]

def rawRow7422 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key151, -6), (key90, -6), (key90, 2), (key84, 2), (key151, 2), (key7, 2), (key1, 2), (key151, 2), (key84, 2), (key202, 2), (key193, 2), (key7, 2), (key151, 2), (key90, 2)]

def rawRow7423 : Integer.Sparse Key := [(key84, -6), (key151, -6), (key90, -6), (key90, -6), (key84, 2), (key151, 2), (key90, 2), (key84, 2), (key151, 2), (key1, 2), (key202, 2), (key7, 2), (key151, 2), (key90, 2), (key7, 2), (key151, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7424 : Integer.Sparse Key := [(key151, -6), (key84, -6), (key90, -6), (key90, -6), (key151, 2), (key84, 2), (key90, 2), (key151, 2), (key84, 2), (key202, 2), (key1, 2), (key151, 2), (key7, 2), (key90, 2), (key151, 2), (key7, 2)]

def rawRow7425 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key84, -6), (key90, -6), (key90, 2), (key151, 2), (key84, 2), (key193, 2), (key202, 2), (key7, 2), (key151, 2), (key1, 2), (key84, 2), (key151, 2), (key7, 2), (key90, 2)]

def rawRow7426 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key84, -6), (key90, -6), (key151, 2), (key90, 2), (key84, 2), (key202, 2), (key193, 2), (key151, 2), (key7, 2), (key84, 2), (key1, 2), (key151, 2), (key90, 2), (key7, 2)]

def rawRow7427 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key151, -6), (key84, -6), (key193, 2), (key193, 2), (key202, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key1, 2), (key84, 2), (key84, 2)]

def rawRow7428 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key90, -6), (key84, -6), (key193, 2), (key202, 2), (key193, 2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key84, 2), (key1, 2), (key84, 2)]

def rawRow7429 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key90, -6), (key84, -6), (key202, 2), (key193, 2), (key193, 2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key84, 2), (key84, 2), (key1, 2)]

def rawRow7430 : Integer.Sparse Key := [(key2377, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2389, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2518, -2)]

def rawRow7431 : Integer.Sparse Key := [(key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

def rawRow7432 : Integer.Sparse Key := [(key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

def rawRow7433 : Integer.Sparse Key := [(key2502, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

def rawRow7434 : Integer.Sparse Key := [(key2377, 2), (key2389, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2479, 2), (key2436, 2), (key2436, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2)]

def rawRow7435 : Integer.Sparse Key := [(key2389, 2), (key2377, 2), (key2389, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2377, -2), (key2389, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2)]

def rawRow7436 : Integer.Sparse Key := [(key2389, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2436, 2), (key2389, -2), (key2377, -2), (key2377, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2502, -2), (key2436, -2)]

def rawRow7437 : Integer.Sparse Key := [(key2405, 2), (key2436, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2389, 2), (key2389, 2), (key2479, 2), (key2479, 2), (key2518, 2), (key2518, 2), (key2405, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

def rawRow7438 : Integer.Sparse Key := [(key2436, 2), (key2405, 2), (key2436, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2405, -2), (key2436, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

def rawRow7439 : Integer.Sparse Key := [(key2436, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2389, 2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

def rawRow7440 : Integer.Sparse Key := [(key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2518, 2), (key2377, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2436, 2), (key2502, 2), (key2471, -2), (key2479, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, -2), (key2405, -2), (key2471, -2)]

def rawRow7441 : Integer.Sparse Key := [(key2479, 2), (key2518, 2), (key2502, 2), (key2389, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2436, 2), (key2479, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2377, -2), (key2471, -2), (key2405, -2)]

def rawRow7442 : Integer.Sparse Key := [(key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2518, 2), (key2405, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2471, -2), (key2502, -2), (key2479, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, -2), (key2377, -2), (key2471, -2)]

def rawRow7443 : Integer.Sparse Key := [(key2502, 2), (key2518, 2), (key2479, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2479, 2), (key2389, 2), (key2502, -2), (key2471, -2), (key2479, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2405, -2), (key2471, -2), (key2377, -2)]

def rawRow7444 : Integer.Sparse Key := [(key2518, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2479, 2), (key2502, 2), (key2389, 2), (key2436, 2), (key2377, 2), (key2405, 2), (key2479, -2), (key2502, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2471, -2), (key2377, -2), (key2405, -2)]

def rawRow7445 : Integer.Sparse Key := [(key2518, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2502, 2), (key2479, 2), (key2436, 2), (key2389, 2), (key2405, 2), (key2377, 2), (key2502, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2471, -2), (key2405, -2), (key2377, -2)]

def rawRow7450 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1024, 6), (key1102, 6), (key1102, 6)]

def rawRow7451 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1024, 6), (key1102, 6)]

def rawRow7452 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1102, 6), (key1024, 6)]

def rawRow7453 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key989, 6), (key1102, 6), (key1102, 6)]

def rawRow7454 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key989, 6), (key1102, 6)]

def rawRow7455 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key989, 6)]

def rawRow7456 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1024, 6), (key1102, 6)]

def rawRow7457 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1024, 6)]

def rawRow7458 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key989, 6), (key1102, 6)]

def rawRow7459 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key1102, 6), (key989, 6)]

def rawRow7460 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key989, 6), (key1024, 6)]

def rawRow7461 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key1024, 6), (key989, 6)]

def rawRow7462 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1030, -6), (key1067, -6), (key995, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1146, 2)]

def rawRow7463 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1067, -6), (key1030, -6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2)]

def rawRow7464 : Integer.Sparse Key := [(key1030, -6), (key1067, -6), (key1030, -6), (key1030, -6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2)]

def rawRow7465 : Integer.Sparse Key := [(key1067, -6), (key1030, -6), (key1030, -6), (key1030, -6), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2)]

def rawRow7466 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1119, -6), (key1146, -6), (key995, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key1146, 2)]

def rawRow7467 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1108, -6), (key1146, -6), (key995, 2), (key1011, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key1067, 2), (key1146, 2)]

def rawRow7468 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1108, -6), (key1146, -6), (key1011, 2), (key995, 2), (key995, 2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1146, 2), (key1146, 2), (key1067, 2)]

def rawRow7469 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1146, -6), (key1119, -6), (key1030, 2), (key1030, 2), (key1067, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1119, 2)]

def rawRow7470 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1108, -6), (key1119, -6), (key1030, 2), (key1067, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1011, 2), (key1119, 2)]

def rawRow7471 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1108, -6), (key1119, -6), (key1067, 2), (key1030, 2), (key1030, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1119, 2), (key1119, 2), (key1011, 2)]

def rawRow7472 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1146, -6), (key1108, -6), (key1108, 2), (key1119, 2), (key1146, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key995, 2), (key1030, 2), (key1108, 2)]

def rawRow7473 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1146, -6), (key1108, -6), (key1119, 2), (key1108, 2), (key1146, 2), (key1011, 2), (key995, 2), (key1119, 2), (key1030, 2), (key1146, 2), (key1067, 2), (key995, 2), (key1108, 2), (key1030, 2)]

def rawRow7474 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1119, -6), (key1108, -6), (key1108, 2), (key1146, 2), (key1119, 2), (key1030, 2), (key1067, 2), (key995, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1030, 2), (key995, 2), (key1108, 2)]

def rawRow7475 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1119, -6), (key1108, -6), (key1146, 2), (key1108, 2), (key1119, 2), (key1067, 2), (key1030, 2), (key1146, 2), (key995, 2), (key1119, 2), (key1011, 2), (key1030, 2), (key1108, 2), (key995, 2)]

def rawRow7476 : Integer.Sparse Key := [(key1119, -6), (key1146, -6), (key1108, -6), (key1108, -6), (key1119, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1146, 2), (key1011, 2), (key1067, 2), (key995, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1030, 2)]

def rawRow7477 : Integer.Sparse Key := [(key1146, -6), (key1119, -6), (key1108, -6), (key1108, -6), (key1146, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1119, 2), (key1067, 2), (key1011, 2), (key1030, 2), (key995, 2), (key1108, 2), (key1030, 2), (key995, 2)]

def rawRow7478 : Integer.Sparse Key := [(key2606, -6), (key2799, -6), (key2799, -6), (key2799, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

def rawRow7479 : Integer.Sparse Key := [(key2799, -6), (key2606, -6), (key2799, -6), (key2799, -6), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow7480 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2606, -6), (key2799, -6), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow7481 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2799, -6), (key2606, -6), (key2849, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow7482 : Integer.Sparse Key := [(key2622, -6), (key2696, -6), (key2849, -6), (key2849, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2696, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

def rawRow7483 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2696, -6), (key2849, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

def rawRow7484 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2849, -6), (key2696, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2696, 2), (key2661, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

def rawRow7485 : Integer.Sparse Key := [(key2696, -6), (key2622, -6), (key2849, -6), (key2849, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2799, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow7486 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2622, -6), (key2849, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2606, 2), (key2799, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow7487 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2849, -6), (key2622, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2799, 2), (key2606, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow7488 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2696, -6), (key2849, -6), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2849, 2), (key2606, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, 2), (key2799, 2)]

def rawRow7489 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2849, -6), (key2696, -6), (key2776, 2), (key2849, 2), (key2799, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2776, 2)]

def rawRow7490 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2622, -6), (key2849, -6), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2849, 2), (key2661, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2622, 2), (key2696, 2)]

def rawRow7491 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2849, -6), (key2622, -6), (key2799, 2), (key2849, 2), (key2776, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2606, 2), (key2696, 2), (key2622, 2)]

def rawRow7492 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2622, -6), (key2696, -6), (key2849, 2), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2776, 2), (key2799, 2), (key2622, 2), (key2696, 2), (key2606, 2), (key2661, 2)]

def rawRow7493 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2696, -6), (key2622, -6), (key2849, 2), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2799, 2), (key2776, 2), (key2696, 2), (key2622, 2), (key2661, 2), (key2606, 2)]

def rawRow7494 : Integer.Sparse Key := [(key2452, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2519, 2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

def rawRow7495 : Integer.Sparse Key := [(key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2530, -2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

def rawRow7496 : Integer.Sparse Key := [(key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

def rawRow7497 : Integer.Sparse Key := [(key2519, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2528, -2)]

def rawRow7498 : Integer.Sparse Key := [(key2357, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2528, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2560, 2), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

def rawRow7499 : Integer.Sparse Key := [(key2361, 2), (key2363, 2), (key2357, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

def rawRow7500 : Integer.Sparse Key := [(key2366, 2), (key2361, 2), (key2361, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2560, 2), (key2560, 2), (key2530, 2), (key2530, 2), (key2528, 2), (key2528, 2), (key2363, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

def rawRow7501 : Integer.Sparse Key := [(key2456, 2), (key2517, 2), (key2523, 2), (key2357, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2519, 2), (key2530, 2), (key2560, 2), (key2452, -2), (key2458, -2), (key2530, -2), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2363, -2), (key2458, -2), (key2519, -2)]

def rawRow7502 : Integer.Sparse Key := [(key2456, 2), (key2523, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2528, 2), (key2363, 2), (key2357, 2), (key2519, 2), (key2452, 2), (key2560, 2), (key2530, 2), (key2458, -2), (key2452, -2), (key2530, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, -2), (key2519, -2), (key2458, -2)]

def rawRow7503 : Integer.Sparse Key := [(key2517, 2), (key2456, 2), (key2523, 2), (key2517, 2), (key2357, 2), (key2560, 2), (key2452, 2), (key2530, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2452, -2), (key2530, -2), (key2458, -2), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2458, -2), (key2363, -2), (key2519, -2)]

def rawRow7504 : Integer.Sparse Key := [(key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2519, 2), (key2363, 2), (key2530, -2), (key2452, -2), (key2458, -2), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2458, -2), (key2519, -2), (key2363, -2)]

def rawRow7505 : Integer.Sparse Key := [(key2523, 2), (key2456, 2), (key2517, 2), (key2579, 2), (key2361, 2), (key2517, 2), (key2519, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2357, 2), (key2452, 2), (key2458, -2), (key2530, -2), (key2452, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, -2), (key2363, -2), (key2458, -2)]

def rawRow7506 : Integer.Sparse Key := [(key2523, 2), (key2517, 2), (key2456, 2), (key2579, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2519, 2), (key2530, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2452, -2), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2519, -2), (key2458, -2), (key2363, -2)]

def rawRow7507 : Integer.Sparse Key := [(key2567, 2), (key2579, 2), (key2579, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2361, 2), (key2361, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2363, -2), (key2458, -2), (key2458, -2), (key2530, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2452, -2)]

def rawRow7508 : Integer.Sparse Key := [(key2579, 2), (key2567, 2), (key2579, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2357, -2), (key2452, -2)]

def rawRow7509 : Integer.Sparse Key := [(key2579, 2), (key2579, 2), (key2567, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2517, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2361, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2530, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2363, -2), (key2452, -2), (key2452, -2), (key2357, -2)]

def rawRow7510 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

def rawRow7511 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

def rawRow7512 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

def rawRow7513 : Integer.Sparse Key := [(key970, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow7514 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

def rawRow7515 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

def rawRow7516 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

def rawRow7517 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1226, 6)]

def rawRow7518 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1226, 6), (key1084, 6)]

def rawRow7519 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1226, 6)]

def rawRow7520 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6)]

def rawRow7521 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6)]

def rawRow7522 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key970, 6)]

def rawRow7523 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow7524 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow7525 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow7526 : Integer.Sparse Key := [(key971, -6), (key979, -6), (key979, -6), (key979, -6), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2)]

def rawRow7527 : Integer.Sparse Key := [(key979, -6), (key971, -6), (key979, -6), (key979, -6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1093, 2)]

def rawRow7528 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key971, -6), (key979, -6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2)]

def rawRow7529 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key979, -6), (key971, -6), (key1228, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow7530 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1093, -6), (key1164, -6), (key971, 2), (key979, 2), (key979, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1164, 2), (key1164, 2), (key1245, 2)]

def rawRow7531 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1093, -6), (key1164, -6), (key979, 2), (key971, 2), (key979, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key1245, 2), (key1164, 2)]

def rawRow7532 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1085, -6), (key1164, -6), (key979, 2), (key979, 2), (key971, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key1164, 2)]

def rawRow7533 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1164, -6), (key1093, -6), (key1085, 2), (key1093, 2), (key1164, 2), (key971, 2), (key979, 2), (key1085, 2), (key1228, 2), (key1164, 2), (key1245, 2), (key979, 2), (key1093, 2), (key1228, 2)]

def rawRow7534 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1164, -6), (key1093, -6), (key1093, 2), (key1085, 2), (key1164, 2), (key979, 2), (key971, 2), (key1228, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key979, 2), (key1228, 2), (key1093, 2)]

def rawRow7535 : Integer.Sparse Key := [(key1085, -6), (key1164, -6), (key1093, -6), (key1093, -6), (key1085, 2), (key1164, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key971, 2), (key1245, 2), (key979, 2), (key1228, 2), (key1093, 2), (key979, 2), (key1228, 2)]

def rawRow7536 : Integer.Sparse Key := [(key1164, -6), (key1085, -6), (key1093, -6), (key1093, -6), (key1164, 2), (key1085, 2), (key1093, 2), (key1164, 2), (key1085, 2), (key1245, 2), (key971, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1228, 2), (key979, 2)]

def rawRow7537 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1085, -6), (key1093, -6), (key1093, 2), (key1164, 2), (key1085, 2), (key1228, 2), (key1245, 2), (key979, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1228, 2), (key979, 2), (key1093, 2)]

def rawRow7538 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1085, -6), (key1093, -6), (key1164, 2), (key1093, 2), (key1085, 2), (key1245, 2), (key1228, 2), (key1164, 2), (key979, 2), (key1085, 2), (key971, 2), (key1228, 2), (key1093, 2), (key979, 2)]

def rawRow7539 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1164, -6), (key1085, -6), (key1228, 2), (key1228, 2), (key1245, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow7540 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1093, -6), (key1085, -6), (key1228, 2), (key1245, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow7541 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1093, -6), (key1085, -6), (key1245, 2), (key1228, 2), (key1228, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1085, 2), (key1085, 2), (key971, 2)]

def rawRow7542 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2400, -6), (key2432, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

def rawRow7543 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2432, -6), (key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

def rawRow7544 : Integer.Sparse Key := [(key2400, -6), (key2432, -6), (key2400, -6), (key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

def rawRow7545 : Integer.Sparse Key := [(key2432, -6), (key2400, -6), (key2400, -6), (key2400, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

def rawRow7546 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2466, -6), (key2498, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2400, 2), (key2432, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

def rawRow7547 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2498, -6), (key2466, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 2), (key2432, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

def rawRow7548 : Integer.Sparse Key := [(key2372, -6), (key2498, -6), (key2466, -6), (key2466, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2400, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

def rawRow7549 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2466, -6), (key2498, -6), (key2400, 2), (key2466, 2), (key2475, 2), (key2372, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2432, 2), (key2475, 2), (key2498, 2)]

def rawRow7550 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2498, -6), (key2466, -6), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2466, 2), (key2385, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2498, 2), (key2475, 2)]

def rawRow7551 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2372, -6), (key2498, -6), (key2466, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2400, 2), (key2475, 2), (key2372, 2), (key2498, 2), (key2385, 2), (key2432, 2)]

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

def rawRow7552 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2498, -6), (key2372, -6), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2475, 2), (key2400, 2), (key2498, 2), (key2372, 2), (key2432, 2), (key2385, 2)]

def rawRow7553 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2372, -6), (key2466, -6), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2432, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2372, 2), (key2400, 2)]

def rawRow7554 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2466, -6), (key2372, -6), (key2475, 2), (key2466, 2), (key2400, 2), (key2498, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2385, 2), (key2400, 2), (key2372, 2)]

def rawRow7555 : Integer.Sparse Key := [(key2498, -6), (key2372, -6), (key2466, -6), (key2466, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2475, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

def rawRow7556 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2372, -6), (key2466, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 2), (key2385, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

def rawRow7557 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2466, -6), (key2372, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2475, 2), (key2385, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

def rawRow7558 : Integer.Sparse Key := [(key2353, -6), (key2359, -6), (key2359, -6), (key2359, -6), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2)]

def rawRow7559 : Integer.Sparse Key := [(key2359, -6), (key2353, -6), (key2359, -6), (key2359, -6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2)]

def rawRow7560 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2353, -6), (key2359, -6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2)]

def rawRow7561 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2359, -6), (key2353, -6), (key2515, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2448, 2)]

def rawRow7562 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2454, -6), (key2515, -6), (key2353, 2), (key2359, 2), (key2359, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2566, 2), (key2566, 2), (key2578, 2)]

def rawRow7563 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2454, -6), (key2515, -6), (key2359, 2), (key2353, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2566, 2), (key2578, 2), (key2566, 2)]

def rawRow7564 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2448, -6), (key2515, -6), (key2359, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2566, 2)]

def rawRow7565 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2515, -6), (key2454, -6), (key2448, 2), (key2454, 2), (key2515, 2), (key2353, 2), (key2359, 2), (key2448, 2), (key2515, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2454, 2), (key2515, 2)]

def rawRow7566 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2515, -6), (key2454, -6), (key2454, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2359, 2), (key2515, 2), (key2454, 2)]

def rawRow7567 : Integer.Sparse Key := [(key2448, -6), (key2515, -6), (key2454, -6), (key2454, -6), (key2448, 2), (key2515, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2353, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2454, 2), (key2359, 2), (key2515, 2)]

def rawRow7568 : Integer.Sparse Key := [(key2515, -6), (key2448, -6), (key2454, -6), (key2454, -6), (key2515, 2), (key2448, 2), (key2454, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2353, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2515, 2), (key2359, 2)]

def rawRow7569 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2448, -6), (key2454, -6), (key2454, 2), (key2515, 2), (key2448, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2454, 2)]

def rawRow7570 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2448, -6), (key2454, -6), (key2515, 2), (key2454, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2515, 2), (key2359, 2), (key2448, 2), (key2353, 2), (key2515, 2), (key2454, 2), (key2359, 2)]

def rawRow7571 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2515, -6), (key2448, -6), (key2566, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow7572 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2454, -6), (key2448, -6), (key2566, 2), (key2578, 2), (key2566, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow7573 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2454, -6), (key2448, -6), (key2578, 2), (key2566, 2), (key2566, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow7610 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

def rawRow7611 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

def rawRow7612 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

def rawRow7613 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1230, 6)]

def rawRow7614 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1104, 6)]

def rawRow7615 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1230, 6)]

def rawRow7616 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key991, 6)]

def rawRow7617 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1104, 6)]

def rawRow7618 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key991, 6)]

def rawRow7619 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1104, 6)]

def rawRow7620 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1104, 6)]

def rawRow7621 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key991, 6)]

def rawRow7622 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

def rawRow7623 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

def rawRow7624 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

def rawRow7625 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

def rawRow7626 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

def rawRow7627 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

def rawRow7628 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1230, 6)]

def rawRow7629 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1230, 6), (key1104, 6)]

def rawRow7630 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1230, 6)]

def rawRow7631 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key991, 6)]

def rawRow7632 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key991, 6), (key1104, 6)]

def rawRow7633 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key991, 6)]

def rawRow7634 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1230, 6)]

def rawRow7635 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1026, 6)]

def rawRow7636 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1230, 6)]

def rawRow7637 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key991, 6)]

def rawRow7638 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1026, 6)]

def rawRow7639 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key991, 6)]

def rawRow7640 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1026, 6), (key1104, 6)]

def rawRow7641 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1026, 6)]

def rawRow7642 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key991, 6), (key1104, 6)]

def rawRow7643 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key991, 6)]

def rawRow7644 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1026, 6)]

def rawRow7645 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key991, 6)]

def rawRow7646 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1036, -6), (key1071, -6), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, 2), (key1150, 2), (key1242, 2)]

def rawRow7647 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1036, -6), (key1071, -6), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1242, 2), (key1150, 2)]

def rawRow7648 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1028, -6), (key1071, -6), (key1001, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1150, 2)]

def rawRow7649 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1071, -6), (key1036, -6), (key1106, 2), (key1114, 2), (key1150, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1232, 2)]

def rawRow7650 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1071, -6), (key1036, -6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1114, 2)]

def rawRow7651 : Integer.Sparse Key := [(key1028, -6), (key1071, -6), (key1036, -6), (key1036, -6), (key1106, 2), (key1150, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1114, 2), (key1001, 2), (key1232, 2)]

def rawRow7652 : Integer.Sparse Key := [(key1071, -6), (key1028, -6), (key1036, -6), (key1036, -6), (key1150, 2), (key1106, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1232, 2), (key1001, 2)]

def rawRow7653 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1028, -6), (key1036, -6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key1114, 2)]

def rawRow7654 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1028, -6), (key1036, -6), (key1150, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1232, 2), (key1114, 2), (key1001, 2)]

def rawRow7655 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1071, -6), (key1028, -6), (key1232, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow7656 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1036, -6), (key1028, -6), (key1232, 2), (key1242, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow7657 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1036, -6), (key1028, -6), (key1242, 2), (key1232, 2), (key1232, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2)]

def rawRow7658 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1123, -6), (key1150, -6), (key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, 2), (key1150, 2), (key1242, 2)]

def rawRow7659 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1123, -6), (key1150, -6), (key1001, 2), (key993, 2), (key1015, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, 2), (key1242, 2), (key1150, 2)]

def rawRow7660 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1114, -6), (key1150, -6), (key993, 2), (key1015, 2), (key1001, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, 2), (key1071, 2), (key1242, 2)]

def rawRow7661 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1114, -6), (key1150, -6), (key1015, 2), (key993, 2), (key1001, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, 2), (key1242, 2), (key1071, 2)]

def rawRow7662 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1106, -6), (key1150, -6), (key1001, 2), (key1015, 2), (key993, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, 2), (key1071, 2), (key1150, 2)]

def rawRow7663 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1106, -6), (key1150, -6), (key1015, 2), (key1001, 2), (key993, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1071, 2)]

def rawRow7664 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1150, -6), (key1123, -6), (key1028, 2), (key1036, 2), (key1071, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1015, 2), (key1123, 2), (key1235, 2)]

def rawRow7665 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1150, -6), (key1123, -6), (key1036, 2), (key1028, 2), (key1071, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1015, 2), (key1235, 2), (key1123, 2)]

def rawRow7666 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1114, -6), (key1123, -6), (key1028, 2), (key1071, 2), (key1036, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1123, 2), (key1015, 2), (key1235, 2)]

def rawRow7667 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1114, -6), (key1123, -6), (key1071, 2), (key1028, 2), (key1036, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1123, 2), (key1235, 2), (key1015, 2)]

def rawRow7668 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1106, -6), (key1123, -6), (key1036, 2), (key1071, 2), (key1028, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1235, 2), (key1015, 2), (key1123, 2)]

def rawRow7669 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1106, -6), (key1123, -6), (key1071, 2), (key1036, 2), (key1028, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1235, 2), (key1123, 2), (key1015, 2)]

def rawRow7670 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1150, -6), (key1114, -6), (key1106, 2), (key1123, 2), (key1150, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1235, 2), (key1071, 2), (key1242, 2), (key1001, 2), (key1036, 2), (key1232, 2)]

def rawRow7671 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1150, -6), (key1114, -6), (key1123, 2), (key1106, 2), (key1150, 2), (key1015, 2), (key993, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key1071, 2), (key1001, 2), (key1232, 2), (key1036, 2)]

def rawRow7672 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1123, -6), (key1114, -6), (key1106, 2), (key1150, 2), (key1123, 2), (key1028, 2), (key1071, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key1036, 2), (key1001, 2), (key1232, 2)]

def rawRow7673 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1123, -6), (key1114, -6), (key1150, 2), (key1106, 2), (key1123, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1235, 2), (key1015, 2), (key1036, 2), (key1232, 2), (key1001, 2)]

def rawRow7674 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1106, -6), (key1114, -6), (key1123, 2), (key1150, 2), (key1106, 2), (key1235, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key993, 2), (key1028, 2), (key1232, 2), (key1001, 2), (key1036, 2)]

def rawRow7675 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1106, -6), (key1114, -6), (key1150, 2), (key1123, 2), (key1106, 2), (key1242, 2), (key1235, 2), (key1071, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1232, 2), (key1036, 2), (key1001, 2)]

def rawRow7676 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1150, -6), (key1106, -6), (key1232, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key993, 2), (key1028, 2), (key1106, 2)]

def rawRow7677 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1150, -6), (key1106, -6), (key1235, 2), (key1232, 2), (key1242, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key993, 2), (key1106, 2), (key1028, 2)]

def rawRow7678 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1123, -6), (key1106, -6), (key1232, 2), (key1242, 2), (key1235, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1028, 2), (key993, 2), (key1106, 2)]

def rawRow7679 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1123, -6), (key1106, -6), (key1242, 2), (key1232, 2), (key1235, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1028, 2), (key1106, 2), (key993, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7680 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1114, -6), (key1106, -6), (key1235, 2), (key1242, 2), (key1232, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow7681 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1114, -6), (key1106, -6), (key1242, 2), (key1235, 2), (key1232, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key993, 2)]

def rawRow7682 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2803, -6), (key2824, -6), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow7683 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2824, -6), (key2803, -6), (key2626, 2), (key2635, 2), (key2626, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow7684 : Integer.Sparse Key := [(key2610, -6), (key2824, -6), (key2803, -6), (key2803, -6), (key2635, 2), (key2626, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow7685 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2803, -6), (key2824, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2626, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow7686 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2824, -6), (key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2853, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow7687 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2610, -6), (key2824, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow7688 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2824, -6), (key2610, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow7689 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2610, -6), (key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow7690 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2803, -6), (key2610, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow7691 : Integer.Sparse Key := [(key2824, -6), (key2610, -6), (key2803, -6), (key2803, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow7692 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2610, -6), (key2803, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow7693 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2803, -6), (key2610, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow7694 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2853, -6), (key2865, -6), (key2610, 2), (key2626, 2), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow7695 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2865, -6), (key2853, -6), (key2610, 2), (key2635, 2), (key2626, 2), (key2665, 2), (key2721, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow7696 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2780, -6), (key2865, -6), (key2626, 2), (key2610, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2721, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow7697 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2865, -6), (key2780, -6), (key2626, 2), (key2635, 2), (key2610, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow7698 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2780, -6), (key2853, -6), (key2635, 2), (key2610, 2), (key2626, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow7699 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2853, -6), (key2780, -6), (key2635, 2), (key2626, 2), (key2610, 2), (key2721, 2), (key2700, 2), (key2665, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow7700 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2853, -6), (key2865, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2610, 2), (key2803, 2), (key2824, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow7701 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2865, -6), (key2853, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2610, 2), (key2824, 2), (key2803, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow7702 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2626, -6), (key2865, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 2), (key2610, 2), (key2824, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow7703 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2865, -6), (key2626, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow7704 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2626, -6), (key2853, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow7705 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2853, -6), (key2626, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow7706 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2780, -6), (key2865, -6), (key2700, 2), (key2803, 2), (key2855, 2), (key2626, 2), (key2780, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2721, 2), (key2789, 2), (key2824, 2)]

def rawRow7707 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2865, -6), (key2780, -6), (key2700, 2), (key2855, 2), (key2803, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2635, 2), (key2610, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2789, 2)]

def rawRow7708 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2626, -6), (key2865, -6), (key2803, 2), (key2700, 2), (key2855, 2), (key2780, 2), (key2626, 2), (key2865, 2), (key2665, 2), (key2789, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2721, 2)]

def rawRow7709 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2865, -6), (key2626, -6), (key2803, 2), (key2855, 2), (key2700, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2721, 2), (key2635, 2)]

def rawRow7710 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2626, -6), (key2780, -6), (key2855, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2721, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2610, 2), (key2665, 2)]

def rawRow7711 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2780, -6), (key2626, -6), (key2855, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2780, 2), (key2626, 2), (key2824, 2), (key2721, 2), (key2789, 2), (key2635, 2), (key2665, 2), (key2610, 2)]

def rawRow7712 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2780, -6), (key2853, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2635, 2), (key2789, 2), (key2855, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow7713 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2853, -6), (key2780, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow7714 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2626, -6), (key2853, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2789, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow7715 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2853, -6), (key2626, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow7716 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2626, -6), (key2780, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow7717 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2780, -6), (key2626, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 2), (key2789, 2), (key2635, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2404, -6), (key2435, -6), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, 2), (key3019, 2), (key3028, 2)]

def rawRow7719 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2404, -6), (key2435, -6), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key3028, 2), (key3019, 2)]

def rawRow7720 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2398, -6), (key2435, -6), (key2589, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key3019, 2)]

def rawRow7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2435, -6), (key2404, -6), (key2839, 2), (key2845, 2), (key3019, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2589, 2), (key2845, 2), (key2876, 2)]

def rawRow7722 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2435, -6), (key2404, -6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2589, 2), (key2876, 2), (key2845, 2)]

def rawRow7723 : Integer.Sparse Key := [(key2398, -6), (key2435, -6), (key2404, -6), (key2404, -6), (key2839, 2), (key3019, 2), (key2845, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2845, 2), (key2589, 2), (key2876, 2)]

def rawRow7724 : Integer.Sparse Key := [(key2435, -6), (key2398, -6), (key2404, -6), (key2404, -6), (key3019, 2), (key2839, 2), (key2845, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2845, 2), (key2876, 2), (key2589, 2)]

def rawRow7725 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2398, -6), (key2404, -6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2876, 2), (key2589, 2), (key2845, 2)]

def rawRow7726 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2398, -6), (key2404, -6), (key3019, 2), (key2845, 2), (key2839, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2876, 2), (key2845, 2), (key2589, 2)]

def rawRow7727 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2435, -6), (key2398, -6), (key2876, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key2589, 2), (key2845, 2), (key2845, 2), (key3019, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow7728 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2404, -6), (key2398, -6), (key2876, 2), (key3028, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow7729 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2404, -6), (key2398, -6), (key3028, 2), (key2876, 2), (key2876, 2), (key3019, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2589, 2), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow7730 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2370, 2), (key2376, 2), (key2388, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def rawRow7731 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2478, -6), (key2501, -6), (key2376, 2), (key2370, 2), (key2388, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, 2), (key3028, 2), (key3019, 2)]

def rawRow7732 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2470, -6), (key2501, -6), (key2370, 2), (key2388, 2), (key2376, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, 2), (key3005, 2), (key3028, 2)]

def rawRow7733 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2470, -6), (key2501, -6), (key2388, 2), (key2370, 2), (key2376, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, 2), (key3028, 2), (key3005, 2)]

def rawRow7734 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2464, -6), (key2501, -6), (key2376, 2), (key2388, 2), (key2370, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, 2), (key3005, 2), (key3019, 2)]

def rawRow7735 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2464, -6), (key2501, -6), (key2388, 2), (key2376, 2), (key2370, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, 2), (key3019, 2), (key3005, 2)]

def rawRow7736 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2501, -6), (key2478, -6), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2604, 2), (key2916, 2), (key2925, 2)]

def rawRow7737 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2501, -6), (key2478, -6), (key2404, 2), (key2398, 2), (key2435, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2604, 2), (key2925, 2), (key2916, 2)]

def rawRow7738 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2470, -6), (key2478, -6), (key2398, 2), (key2435, 2), (key2404, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2916, 2), (key2604, 2), (key2925, 2)]

def rawRow7739 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2470, -6), (key2478, -6), (key2435, 2), (key2398, 2), (key2404, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2916, 2), (key2925, 2), (key2604, 2)]

def rawRow7740 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2464, -6), (key2478, -6), (key2404, 2), (key2435, 2), (key2398, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2925, 2), (key2604, 2), (key2916, 2)]

def rawRow7741 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2464, -6), (key2478, -6), (key2435, 2), (key2404, 2), (key2398, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2925, 2), (key2916, 2), (key2604, 2)]

def rawRow7742 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2501, -6), (key2470, -6), (key2464, 2), (key2478, 2), (key2501, 2), (key2370, 2), (key2388, 2), (key2762, 2), (key2925, 2), (key3005, 2), (key3028, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

def rawRow7743 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2501, -6), (key2470, -6), (key2478, 2), (key2464, 2), (key2501, 2), (key2388, 2), (key2370, 2), (key2925, 2), (key2762, 2), (key3028, 2), (key3005, 2), (key2589, 2), (key2876, 2), (key2768, 2)]

def rawRow7744 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2478, -6), (key2470, -6), (key2464, 2), (key2501, 2), (key2478, 2), (key2398, 2), (key2435, 2), (key2583, 2), (key3028, 2), (key2604, 2), (key2925, 2), (key2768, 2), (key2589, 2), (key2876, 2)]

def rawRow7745 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2478, -6), (key2470, -6), (key2501, 2), (key2464, 2), (key2478, 2), (key2435, 2), (key2398, 2), (key3028, 2), (key2583, 2), (key2925, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2589, 2)]

def rawRow7746 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2464, -6), (key2470, -6), (key2478, 2), (key2501, 2), (key2464, 2), (key2570, 2), (key2575, 2), (key2388, 2), (key2435, 2), (key2370, 2), (key2762, 2), (key2876, 2), (key2589, 2), (key2768, 2)]

def rawRow7747 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2464, -6), (key2470, -6), (key2501, 2), (key2478, 2), (key2464, 2), (key2575, 2), (key2570, 2), (key2435, 2), (key2388, 2), (key2398, 2), (key2583, 2), (key2876, 2), (key2768, 2), (key2589, 2)]

def rawRow7748 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2501, -6), (key2464, -6), (key2568, 2), (key2570, 2), (key2575, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow7749 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2501, -6), (key2464, -6), (key2570, 2), (key2568, 2), (key2575, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow7750 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2478, -6), (key2464, -6), (key2568, 2), (key2575, 2), (key2570, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow7751 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2478, -6), (key2464, -6), (key2575, 2), (key2568, 2), (key2570, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow7752 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2470, -6), (key2464, -6), (key2570, 2), (key2575, 2), (key2568, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow7753 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2470, -6), (key2464, -6), (key2575, 2), (key2570, 2), (key2568, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow7790 : Integer.Sparse Key := [(key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

def rawRow7791 : Integer.Sparse Key := [(key2360, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2360, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

def rawRow7792 : Integer.Sparse Key := [(key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2)]

def rawRow7793 : Integer.Sparse Key := [(key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2455, -2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2), (key2455, -2)]

def rawRow7794 : Integer.Sparse Key := [(key2516, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2360, 2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2)]

def rawRow7795 : Integer.Sparse Key := [(key968, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

def rawRow7796 : Integer.Sparse Key := [(key1082, -24), (key968, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

def rawRow7797 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key968, 6), (key1082, 6), (key1082, 6)]

def rawRow7798 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key968, 6), (key1082, 6)]

def rawRow7799 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key968, 6)]

def rawRow7800 : Integer.Sparse Key := [(key973, -6), (key973, -6), (key973, -6), (key973, -6), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2)]

def rawRow7801 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1087, -6), (key1160, -6), (key973, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key1160, 2)]

def rawRow7802 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1160, -6), (key1087, -6), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2)]

def rawRow7803 : Integer.Sparse Key := [(key1087, -6), (key1160, -6), (key1087, -6), (key1087, -6), (key1087, 2), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2), (key1087, 2)]

def rawRow7804 : Integer.Sparse Key := [(key1160, -6), (key1087, -6), (key1087, -6), (key1087, -6), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1087, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2)]

def rawRow7805 : Integer.Sparse Key := [(key2396, -6), (key2396, -6), (key2396, -6), (key2396, -6), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

def rawRow7806 : Integer.Sparse Key := [(key2581, -6), (key2837, -6), (key2837, -6), (key2837, -6), (key2368, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

def rawRow7807 : Integer.Sparse Key := [(key2837, -6), (key2581, -6), (key2837, -6), (key2837, -6), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2837, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7808 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2581, -6), (key2837, -6), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2368, 2), (key2396, 2)]

def rawRow7809 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2837, -6), (key2581, -6), (key2837, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2760, 2), (key2581, 2)]

def rawRow7810 : Integer.Sparse Key := [(key2355, -6), (key2355, -6), (key2355, -6), (key2355, -6), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2)]

def rawRow7811 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2450, -6), (key2512, -6), (key2355, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2512, 2)]

def rawRow7812 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2512, -6), (key2450, -6), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2)]

def rawRow7813 : Integer.Sparse Key := [(key2450, -6), (key2512, -6), (key2450, -6), (key2450, -6), (key2450, 2), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2), (key2450, 2)]

def rawRow7814 : Integer.Sparse Key := [(key2512, -6), (key2450, -6), (key2450, -6), (key2450, -6), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2)]

def rawRow7815 : Integer.Sparse Key := [(key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1)]

def rawRow7816 : Integer.Sparse Key := [(key2585, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2873, -2), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1)]

def rawRow7817 : Integer.Sparse Key := [(key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1)]

def rawRow7818 : Integer.Sparse Key := [(key2841, -2), (key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2764, 1)]

def rawRow7819 : Integer.Sparse Key := [(key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2873, 1), (key2841, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2764, 1), (key2585, 1)]

def rawRow7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

def rawRow7821 : Integer.Sparse Key := [(key2446, -24), (key2351, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

def rawRow7822 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2351, 6), (key2446, 6), (key2446, 6)]

def rawRow7823 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2351, 6), (key2446, 6)]

def rawRow7824 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2351, 6)]

def rawRow7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

def rawRow7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

def rawRow7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

def rawRow7840 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

def rawRow7841 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

def rawRow7842 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

def rawRow7843 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

def rawRow7844 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

def rawRow7845 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

def rawRow7846 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

def rawRow7847 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

def rawRow7848 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

def rawRow7849 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1001, -6), (key1015, -6), (key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, 2), (key1123, 2), (key1235, 2)]

def rawRow7850 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1001, -6), (key1015, -6), (key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1123, 2)]

def rawRow7851 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key993, -6), (key1015, -6), (key1036, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1123, 2)]

def rawRow7852 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1015, -6), (key1001, -6), (key1106, 2), (key1114, 2), (key1123, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1232, 2)]

def rawRow7853 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1015, -6), (key1001, -6), (key1114, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1114, 2)]

def rawRow7854 : Integer.Sparse Key := [(key993, -6), (key1015, -6), (key1001, -6), (key1001, -6), (key1106, 2), (key1123, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1036, 2), (key1232, 2)]

def rawRow7855 : Integer.Sparse Key := [(key1015, -6), (key993, -6), (key1001, -6), (key1001, -6), (key1123, 2), (key1106, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1232, 2), (key1036, 2)]

def rawRow7856 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key993, -6), (key1001, -6), (key1114, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1114, 2)]

def rawRow7857 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key993, -6), (key1001, -6), (key1123, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, 2), (key1114, 2), (key1036, 2)]

def rawRow7858 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key1015, -6), (key993, -6), (key1232, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow7859 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key1001, -6), (key993, -6), (key1232, 2), (key1235, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2)]

def rawRow7860 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key1001, -6), (key993, -6), (key1235, 2), (key1232, 2), (key1232, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2)]

def rawRow7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2700, -6), (key2721, -6), (key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2721, -6), (key2700, -6), (key2780, 2), (key2789, 2), (key2780, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow7863 : Integer.Sparse Key := [(key2665, -6), (key2721, -6), (key2700, -6), (key2700, -6), (key2789, 2), (key2780, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow7864 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2700, -6), (key2721, -6), (key2803, 2), (key2853, 2), (key2855, 2), (key2780, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow7865 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2721, -6), (key2700, -6), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow7866 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2665, -6), (key2721, -6), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow7867 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2721, -6), (key2665, -6), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow7868 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2665, -6), (key2700, -6), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow7869 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2700, -6), (key2665, -6), (key2855, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow7870 : Integer.Sparse Key := [(key2721, -6), (key2665, -6), (key2700, -6), (key2700, -6), (key2824, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow7871 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2665, -6), (key2700, -6), (key2865, 2), (key2824, 2), (key2865, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow7872 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2700, -6), (key2665, -6), (key2865, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2376, -6), (key2388, -6), (key2762, 2), (key2768, 2), (key2768, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, 2), (key2916, 2), (key2925, 2)]

def rawRow7874 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2376, -6), (key2388, -6), (key2768, 2), (key2762, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2925, 2), (key2916, 2)]

def rawRow7875 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2370, -6), (key2388, -6), (key2768, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2916, 2)]

def rawRow7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2388, -6), (key2376, -6), (key2839, 2), (key2845, 2), (key2916, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, 2), (key2845, 2), (key2876, 2)]

def rawRow7877 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2388, -6), (key2376, -6), (key2845, 2), (key2839, 2), (key2916, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, 2), (key2876, 2), (key2845, 2)]

def rawRow7878 : Integer.Sparse Key := [(key2370, -6), (key2388, -6), (key2376, -6), (key2376, -6), (key2839, 2), (key2916, 2), (key2845, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, 2), (key2768, 2), (key2876, 2)]

def rawRow7879 : Integer.Sparse Key := [(key2388, -6), (key2370, -6), (key2376, -6), (key2376, -6), (key2916, 2), (key2839, 2), (key2845, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, 2), (key2876, 2), (key2768, 2)]

def rawRow7880 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2370, -6), (key2376, -6), (key2845, 2), (key2916, 2), (key2839, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, 2), (key2768, 2), (key2845, 2)]

def rawRow7881 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2370, -6), (key2376, -6), (key2916, 2), (key2845, 2), (key2839, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, 2), (key2845, 2), (key2768, 2)]

def rawRow7882 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2388, -6), (key2370, -6), (key2876, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2839, 2)]

def rawRow7883 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2376, -6), (key2370, -6), (key2876, 2), (key2925, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2762, 2), (key2839, 2)]

def rawRow7884 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2376, -6), (key2370, -6), (key2925, 2), (key2876, 2), (key2876, 2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, 2), (key2839, 2), (key2762, 2)]

def rawRow7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

def rawRow7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

def rawRow7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

def rawRow7900 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

def rawRow7901 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

def rawRow7902 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

def rawRow7903 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

end MUB6.Certificate.GramRows

end OAI
end


