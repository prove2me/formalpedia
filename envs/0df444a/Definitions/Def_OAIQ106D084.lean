-- Prove2me | Definitions.Def_OAIQ106D084
-- name    : OAIQ106D084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:53:48.091665+00:00
-- url     : https://prove2.me/theorems/ca18fcc4-2c33-4f95-b89e-eed1ec5e386f
-- title:
--   Definitions bundle OAIQ106D084 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1175 declarations of OpenAI's Lean: 1175 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key2357`, `OAI.MUB6.Certificate.GramRows.key2421`, `OAI.MUB6.Certificate.GramRows.key2458`, `OAI.MUB6.Certificate.GramRows.key2461`, `OAI.MUB6.Certificate.GramRows.key2467`, `OAI.MUB6.Certificate.GramRows.key2470`, `OAI.MUB6.Certificate.GramRows.key2842`, `OAI.MUB6.Certificate.GramRows.key3033`, `OAI.MUB6.Certificate.GramRows.key3036`, `OAI.MUB6.Certificate.GramRows.row1765`, `OAI.MUB6.Certificate.GramRows.row1766`, `OAI.MUB6.Certificate.GramRows.row1767`, `OAI.MUB6.Certificate.GramRows.row1768`, `OAI.MUB6.Certificate.GramRows.row1769`, `OAI.MUB6.Certificate.GramRows.row1770`, `OAI.MUB6.Certificate.GramRows.row1771`, `OAI.MUB6.Certificate.GramRows.row1772`, `OAI.MUB6.Certificate.GramRows.row1773`, `OAI.MUB6.Certificate.GramRows.row1774`, `OAI.MUB6.Certificate.GramRows.row1775`, `OAI.MUB6.Certificate.GramRows.row1776`, `OAI.MUB6.Certificate.GramRows.row1777`, `OAI.MUB6.Certificate.GramRows.row1778`, `OAI.MUB6.Certificate.GramRows.row1779`, `OAI.MUB6.Certificate.GramRows.row1780`, `OAI.MUB6.Certificate.GramRows.row1781`, `OAI.MUB6.Certificate.GramRows.row1782`, `OAI.MUB6.Certificate.GramRows.row1783`, `OAI.MUB6.Certificate.GramRows.row1784`, `OAI.MUB6.Certificate.GramRows.row1785`, `OAI.MUB6.Certificate.GramRows.row1786`, `OAI.MUB6.Certificate.GramRows.row1787`, `OAI.MUB6.Certificate.GramRows.row1788`, `OAI.MUB6.Certificate.GramRows.row1789`, `OAI.MUB6.Certificate.GramRows.row1790`, `OAI.MUB6.Certificate.GramRows.row1791`, `OAI.MUB6.Certificate.GramRows.row1792`, `OAI.MUB6.Certificate.GramRows.row1793`, `OAI.MUB6.Certificate.GramRows.row1794`, `OAI.MUB6.Certificate.GramRows.row1795` and 1135 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block19`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block38`, `MutuallyUnbiased_GramRows_Block39`, `MutuallyUnbiased_GramRows_Block40`, `MutuallyUnbiased_GramRows_Block41`, `MutuallyUnbiased_GramRows_Block42`, `MutuallyUnbiased_GramRows_Block43`, `MutuallyUnbiased_GramRows_Block44`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_MixedSemantics_Values15`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D183`, `OAIQ106D184` and `OAIQ106D185`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2357 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2421 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩

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

def key2458 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2461 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key2467 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key2470 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩

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

def key2842 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 2)]⟩

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

def key3033 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩
def key3036 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1765 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

def row1766 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

def row1767 : Integer.Sparse Key := [(key2402, 6), (key2408, -6), (key2468, -6), (key2481, 6), (key2537, 6), (key2542, -6)]

def row1768 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1769 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1770 : Integer.Sparse Key := [(key2402, 2), (key2408, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key3020, -2), (key3029, 2)]

def row1771 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1772 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1773 : Integer.Sparse Key := [(key2380, 2), (key2391, -2), (key2408, 2), (key2481, -2), (key2537, 2), (key2542, -2), (key2596, -2), (key2605, 2), (key2770, -2), (key2847, 2), (key2884, -4), (key2926, 4)]

def row1774 : Integer.Sparse Key := [(key2770, -6), (key2775, 6), (key2847, 6), (key2884, -6), (key2917, -6), (key2926, 6)]

def row1775 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1776 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1777 : Integer.Sparse Key := [(key2770, 2), (key2775, -2), (key2847, -2), (key2884, 2), (key2917, 2), (key2926, -2)]

def row1778 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1779 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1780 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1781 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, -6), (key1677, 6), (key1892, 6), (key1914, -6)]

def row1782 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1783 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1784 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1785 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1786 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1787 : Integer.Sparse Key := [(key1250, -2), (key1269, 2), (key1525, 2), (key1677, -2), (key1892, -2), (key1914, 2)]

def row1788 : Integer.Sparse Key := [(key1250, -6), (key1269, 6), (key1525, 6), (key1677, -6), (key1892, -6), (key1914, 6)]

def row1789 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1790 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

def row1791 : Integer.Sparse Key := [(key1250, 2), (key1269, -2), (key1525, -2), (key1677, 2), (key1892, 2), (key1914, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1792 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1793 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1794 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

def row1795 : Integer.Sparse Key := [(key2376, 6), (key2388, -6), (key2404, -6), (key2435, 6), (key2478, 6), (key2501, -6)]

def row1796 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1797 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1798 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

def row1799 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1800 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1801 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

def row1802 : Integer.Sparse Key := [(key2589, -6), (key2604, 6), (key2768, 6), (key2916, -6), (key3005, -6), (key3019, 6)]

def row1803 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1804 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1805 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

def row1806 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1807 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1808 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1809 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1164, 6), (key1228, 6), (key1245, -6)]

def row1810 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1811 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1812 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1813 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1814 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1815 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

def row1816 : Integer.Sparse Key := [(key971, -6), (key979, 6), (key1085, 6), (key1164, -6), (key1228, -6), (key1245, 6)]

def row1817 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1818 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1819 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

def row1820 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1821 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1822 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1823 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, -6), (key2432, 6), (key2475, 6), (key2498, -6)]

def row1824 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1825 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1826 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1827 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1828 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1829 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

def row1830 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, 6), (key2432, -6), (key2475, -6), (key2498, 6)]

def row1831 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1832 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1833 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

def row1834 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1835 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1836 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1837 : Integer.Sparse Key := [(key1526, 6), (key1534, -6), (key1604, -6), (key1640, 6), (key1679, 6), (key1693, -6)]

def row1838 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1839 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1840 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1841 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1842 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1843 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

def row1844 : Integer.Sparse Key := [(key1526, -6), (key1534, 6), (key1604, 6), (key1640, -6), (key1679, -6), (key1693, 6)]

def row1845 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1846 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1847 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

def row1848 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1849 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1850 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

def row1851 : Integer.Sparse Key := [(key2414, 6), (key2419, -6), (key2487, -6), (key2494, 6), (key2572, 6), (key2573, -6)]

def row1852 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1853 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1854 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

def row1855 : Integer.Sparse Key := [(key2414, -6), (key2419, 6), (key2426, -4), (key2494, -2), (key3033, 4), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1856 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1857 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

def row1858 : Integer.Sparse Key := [(key2414, -6), (key2487, 6), (key3038, 6), (key3130, -6), (key3141, -6), (key3144, 6)]

def row1859 : Integer.Sparse Key := [(key2414, 6), (key3033, -4), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1860 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1861 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

def row1862 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1863 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1864 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1865 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, -6), (key1679, 6), (key1894, 6), (key1916, -6)]

def row1866 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1867 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1868 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1869 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1870 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1871 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

def row1872 : Integer.Sparse Key := [(key1259, -6), (key1271, 6), (key1534, 6), (key1679, -6), (key1894, -6), (key1916, 6)]

def row1873 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1874 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1875 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

def row1876 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1877 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1878 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1879 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1163, 6), (key1227, 6), (key1244, -6)]

def row1880 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1881 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1882 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1883 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1884 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1885 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

def row1886 : Integer.Sparse Key := [(key972, -6), (key978, 6), (key1086, 6), (key1163, -6), (key1227, -6), (key1244, 6)]

def row1887 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1888 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1889 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

def row1890 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1891 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1892 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

def row1893 : Integer.Sparse Key := [(key2374, 6), (key2380, -6), (key2468, -6), (key2505, 6), (key2537, 6), (key2553, -6)]

def row1894 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1895 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1896 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

def row1897 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1898 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1899 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

def row1900 : Integer.Sparse Key := [(key2591, -6), (key2596, 6), (key2847, 6), (key2884, -6), (key3020, -6), (key3029, 6)]

def row1901 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1902 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1903 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

def row1904 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1905 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1906 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

def row1907 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2515, 6), (key2566, 6), (key2578, -6)]

def row1908 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1909 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1910 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

def row1911 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1912 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1913 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

def row1914 : Integer.Sparse Key := [(key2353, -6), (key2359, 6), (key2448, 6), (key2515, -6), (key2566, -6), (key2578, 6)]

def row1915 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1916 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1917 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

def row1918 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1919 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

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

def row1920 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1921 : Integer.Sparse Key := [(key2770, 6), (key2773, -6), (key2847, -6), (key2881, 6), (key2890, 6), (key2911, -6)]

def row1922 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1923 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1924 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1925 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1926 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1927 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

def row1928 : Integer.Sparse Key := [(key2770, -6), (key2773, 6), (key2847, 6), (key2881, -6), (key2890, -6), (key2911, 6)]

def row1929 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1930 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1931 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

def row1932 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1933 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1934 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1935 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, -6), (key1645, 6), (key1762, 6), (key1803, -6)]

def row1936 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1937 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1938 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1939 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1940 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1941 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

def row1942 : Integer.Sparse Key := [(key1249, -6), (key1262, 6), (key1524, 6), (key1645, -6), (key1762, -6), (key1803, 6)]

def row1943 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1944 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1945 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

def row1946 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1947 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1948 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1949 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, -6), (key2888, 6), (key2930, 6), (key2967, -6)]

def row1950 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1951 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1952 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1953 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1954 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1955 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

def row1956 : Integer.Sparse Key := [(key2588, -6), (key2599, 6), (key2767, 6), (key2888, -6), (key2930, -6), (key2967, 6)]

def row1957 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1958 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1959 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

def row1960 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1961 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1962 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1963 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1162, 6), (key1181, 6), (key1218, -6)]

def row1964 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1965 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1966 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1967 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1968 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1969 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

def row1970 : Integer.Sparse Key := [(key972, -6), (key977, 6), (key1086, 6), (key1162, -6), (key1181, -6), (key1218, 6)]

def row1971 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1972 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1973 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

def row1974 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1975 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1976 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1977 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, -6), (key2431, 6), (key2474, 6), (key2497, -6)]

def row1978 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1979 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1980 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1981 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1982 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1983 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

def row1984 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, 6), (key2431, -6), (key2474, -6), (key2497, 6)]

def row1985 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1986 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1987 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

def row1988 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1989 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1990 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1991 : Integer.Sparse Key := [(key1527, 6), (key1532, -6), (key1605, -6), (key1638, 6), (key1649, 6), (key1672, -6)]

def row1992 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1993 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1994 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row1995 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1996 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1997 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

def row1998 : Integer.Sparse Key := [(key1527, -6), (key1532, 6), (key1605, 6), (key1638, -6), (key1649, -6), (key1672, 6)]

def row1999 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2000 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2001 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

def row2002 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2003 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2004 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2005 : Integer.Sparse Key := [(key3034, 6), (key3037, -6), (key3121, -6), (key3129, 6), (key3133, 6), (key3139, -6)]

def row2006 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2007 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2008 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2009 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2010 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2011 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

def row2012 : Integer.Sparse Key := [(key3034, -6), (key3037, 6), (key3121, 6), (key3129, -6), (key3133, -6), (key3139, 6)]

def row2013 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2014 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2015 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

def row2016 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2017 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2018 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2019 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, -6), (key1649, 6), (key1766, 6), (key1807, -6)]

def row2020 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2021 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2022 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2023 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2024 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2025 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

def row2026 : Integer.Sparse Key := [(key1257, -6), (key1266, 6), (key1532, 6), (key1649, -6), (key1766, -6), (key1807, 6)]

def row2027 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2028 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2029 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

def row2030 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2031 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2032 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2033 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1161, 6), (key1179, 6), (key1217, -6)]

def row2034 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2035 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2036 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2037 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2038 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2039 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

def row2040 : Integer.Sparse Key := [(key971, -6), (key975, 6), (key1085, 6), (key1161, -6), (key1179, -6), (key1217, 6)]

def row2041 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2042 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2043 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

def row2044 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2045 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2046 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2047 : Integer.Sparse Key := [(key2591, 6), (key2594, -6), (key2847, -6), (key2881, 6), (key2969, 6), (key2990, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2048 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2049 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2050 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2051 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2052 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2053 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

def row2054 : Integer.Sparse Key := [(key2591, -6), (key2594, 6), (key2847, 6), (key2881, -6), (key2969, -6), (key2990, 6)]

def row2055 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2056 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2057 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

def row2058 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2059 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2060 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2061 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2514, 6), (key2529, 6), (key2559, -6)]

def row2062 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2063 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2064 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2065 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2066 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2067 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

def row2068 : Integer.Sparse Key := [(key2354, -6), (key2358, 6), (key2449, 6), (key2514, -6), (key2529, -6), (key2559, 6)]

def row2069 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2070 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2071 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

def row2072 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2073 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2074 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

def row2075 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2513, 6), (key2527, 6), (key2558, -6)]

def row2076 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2077 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2078 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

def row2079 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2080 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2081 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

def row2082 : Integer.Sparse Key := [(key2353, -6), (key2356, 6), (key2448, 6), (key2513, -6), (key2527, -6), (key2558, 6)]

def row2083 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2084 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2085 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

def row2086 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2087 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2088 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row2089 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2090 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2091 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2092 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2093 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2094 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2095 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2096 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2097 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row2098 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2099 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2100 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2101 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2102 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2103 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2104 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2105 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2106 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2107 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2108 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2109 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row2110 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2111 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2112 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2113 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2114 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2115 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row2116 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2117 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2118 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

def row2119 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2120 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2121 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2122 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2123 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2124 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

def row2125 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2126 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2127 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

def row2128 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2129 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2130 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2131 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2132 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2133 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

def row2134 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2135 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2136 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2137 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2138 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2139 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

def row2140 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2141 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2142 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2143 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2144 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2145 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

def row2146 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2147 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2148 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

def row2149 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2150 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2151 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2152 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2153 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2154 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

def row2155 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2156 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2157 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

def row2158 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2159 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2160 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2161 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2162 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2163 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

def row2164 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2165 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2166 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2167 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2168 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2169 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

def row2170 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2171 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2172 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2173 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2174 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

def row2175 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2176 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2177 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2178 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

def row2179 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2180 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2181 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2182 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2183 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2184 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

def row2185 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2186 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2187 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

def row2188 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2189 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2190 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2191 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2192 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2193 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

def row2194 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2195 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2196 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2197 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2198 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2199 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

def row2200 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2201 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2202 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2203 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2204 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2205 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

def row2206 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2207 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2208 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

def row2209 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2210 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2211 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2212 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2213 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2214 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

def row2215 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2216 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2217 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

def row2218 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2219 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2220 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2221 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2222 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2223 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

def row2224 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2225 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2226 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2227 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2228 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2229 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

def row2230 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2231 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2232 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2233 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2234 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2235 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

def row2236 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2237 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2238 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

def row2239 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2240 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2241 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2242 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2243 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2244 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2245 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2246 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2247 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

def row2248 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2249 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2250 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2251 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2252 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2253 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2254 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2255 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2256 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2257 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2258 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2259 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

def row2260 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2261 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2262 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2263 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2264 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2265 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

def row2266 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2267 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2268 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

def row2269 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2270 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2271 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2272 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2273 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2274 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

def row2275 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2276 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2277 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

def row2278 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2279 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2280 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2281 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2282 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2283 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

def row2284 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2285 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2286 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2287 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2288 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2289 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

def row2290 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2291 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2292 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2293 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2294 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2295 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

def row2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2297 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2298 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

def row2299 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2300 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2301 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2302 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2303 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2304 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

def row2305 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2306 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2307 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

def row2308 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2309 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2310 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2311 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2312 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2313 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

def row2314 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2315 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2316 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2317 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2318 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2319 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

def row2320 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2321 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2322 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2323 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2324 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2325 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

def row2326 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2327 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2328 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

def row2329 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2330 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2331 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2332 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2333 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2334 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

def row2335 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2336 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2337 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

def row2338 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2339 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2340 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2341 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2342 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2343 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

def row2344 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2345 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2346 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2347 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2348 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2349 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

def row2350 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2351 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2352 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2353 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2354 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2355 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

def row2356 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2357 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2358 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

def row2359 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2360 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2361 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2362 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2363 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2364 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

def row2365 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2366 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2367 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

def row2368 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2369 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2370 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2371 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2372 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2373 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

def row2374 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2375 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2376 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2377 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2378 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2379 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

def row2380 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2381 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2382 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2383 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2384 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2385 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

def row2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2387 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2388 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

def row2389 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2390 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2391 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2392 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2393 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2394 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

def row2395 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2396 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2397 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

def row2398 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2399 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2400 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2401 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2402 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2403 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

def row2404 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2405 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2406 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2407 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2408 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2409 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

def row2410 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2411 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2412 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2413 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2414 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2415 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

def row2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2417 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2418 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

def row2419 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2420 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2421 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2422 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2423 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2424 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

def row2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2426 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2427 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

def row2428 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2429 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2430 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2431 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2432 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2433 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

def row2434 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2435 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2436 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2437 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2438 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2439 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row2440 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2441 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2442 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2443 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2444 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2445 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

def row2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2447 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2448 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

def row2449 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2451 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2452 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2453 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2454 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

def row2455 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2456 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2457 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

def row2458 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2459 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2460 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2461 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2462 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2463 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row2464 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2465 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2466 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2467 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2468 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2469 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

def row2470 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2471 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2472 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2473 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2474 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2475 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

def row2476 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2477 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2478 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2479 : Integer.Sparse Key := [(key2175, 6), (key2179, -6), (key2275, -6), (key2281, 6), (key2328, 6), (key2330, -6)]

def row2480 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2481 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2482 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2483 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2484 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2485 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

def row2486 : Integer.Sparse Key := [(key2175, -6), (key2179, 6), (key2275, 6), (key2281, -6), (key2328, -6), (key2330, 6)]

def row2487 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2488 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2489 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

def row2490 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2491 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2492 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2493 : Integer.Sparse Key := [(key754, 6), (key755, -6), (key843, -6), (key844, 6), (key944, 6), (key945, -6)]

def row2494 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2495 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2496 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2497 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2498 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2499 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

def row2500 : Integer.Sparse Key := [(key754, -6), (key755, 6), (key843, 6), (key844, -6), (key944, -6), (key945, 6)]

def row2501 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2502 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2503 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

def row2504 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2505 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2506 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2507 : Integer.Sparse Key := [(key2079, 6), (key2085, -6), (key2176, -6), (key2187, 6), (key2279, 6), (key2287, -6)]

def row2508 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2509 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2510 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2511 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2512 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2513 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

def row2514 : Integer.Sparse Key := [(key2079, -6), (key2085, 6), (key2176, 6), (key2187, -6), (key2279, -6), (key2287, 6)]

def row2515 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2516 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2517 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

def row2518 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2519 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2520 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2521 : Integer.Sparse Key := [(key713, 6), (key715, -6), (key890, -6), (key914, 6), (key959, 6), (key966, -6)]

def row2522 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2523 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2524 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2525 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2526 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2527 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

def row2528 : Integer.Sparse Key := [(key713, -6), (key715, 6), (key890, 6), (key914, -6), (key959, -6), (key966, 6)]

def row2529 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2530 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2531 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

def row2532 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2533 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2534 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2535 : Integer.Sparse Key := [(key2098, 6), (key2099, -6), (key2203, -6), (key2206, 6), (key2318, 6), (key2321, -6)]

def row2536 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2537 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2538 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2539 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2540 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2541 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

def row2542 : Integer.Sparse Key := [(key2098, -6), (key2099, 6), (key2203, 6), (key2206, -6), (key2318, -6), (key2321, 6)]

def row2543 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2544 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2545 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

def row2546 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2547 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2548 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2549 : Integer.Sparse Key := [(key817, 6), (key818, -6), (key897, -6), (key902, 6), (key960, 6), (key962, -6)]

def row2550 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2551 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2552 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2553 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2554 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2555 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

def row2556 : Integer.Sparse Key := [(key817, -6), (key818, 6), (key897, 6), (key902, -6), (key960, -6), (key962, 6)]

def row2557 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2558 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

def row2559 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2560 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2561 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2562 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2563 : Integer.Sparse Key := [(key2182, 6), (key2183, -6), (key2284, -6), (key2285, 6), (key2345, 6), (key2346, -6)]

def row2564 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2565 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2566 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2567 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2568 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2569 : Integer.Sparse Key := [(key2182, -2), (key2183, 2), (key2284, 2), (key2285, -2), (key2345, -2), (key2346, 2)]

def row2570 : Integer.Sparse Key := [(key2182, -6), (key2183, 6), (key2284, 6), (key2285, -6), (key2345, -6), (key2346, 6)]

def row2571 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2572 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2573 : Integer.Sparse Key := [(key2182, 2), (key2183, -2), (key2284, -2), (key2285, 2), (key2345, 2), (key2346, -2)]

def row2574 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2575 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2576 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2577 : Integer.Sparse Key := [(key738, 6), (key743, -6), (key818, -6), (key825, 6), (key902, 6), (key908, -6)]

def row2578 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2579 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2580 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2581 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2582 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2583 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key818, 2), (key825, -2), (key902, -2), (key908, 2)]

def row2584 : Integer.Sparse Key := [(key738, -6), (key743, 6), (key818, 6), (key825, -6), (key902, -6), (key908, 6)]

def row2585 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2586 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2587 : Integer.Sparse Key := [(key738, 2), (key743, -2), (key818, -2), (key825, 2), (key902, 2), (key908, -2)]

def row2588 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2589 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2590 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2591 : Integer.Sparse Key := [(key721, 6), (key722, -6), (key921, -6), (key939, 6), (key959, 6), (key966, -6)]

def row2592 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2593 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2594 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2595 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2596 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2597 : Integer.Sparse Key := [(key721, -2), (key722, 2), (key921, 2), (key939, -2), (key959, -2), (key966, 2)]

def row2598 : Integer.Sparse Key := [(key721, -6), (key722, 6), (key921, 6), (key939, -6), (key959, -6), (key966, 6)]

def row2599 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2600 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2601 : Integer.Sparse Key := [(key721, 2), (key722, -2), (key921, -2), (key939, 2), (key959, 2), (key966, -2)]

def row2602 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2603 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2604 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2605 : Integer.Sparse Key := [(key2078, 6), (key2082, -6), (key2275, -6), (key2289, 6), (key2328, 6), (key2333, -6)]

def row2606 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2607 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2608 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2609 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2610 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2611 : Integer.Sparse Key := [(key2078, -2), (key2082, 2), (key2275, 2), (key2289, -2), (key2328, -2), (key2333, 2)]

def row2612 : Integer.Sparse Key := [(key2078, -6), (key2082, 6), (key2275, 6), (key2289, -6), (key2328, -6), (key2333, 6)]

def row2613 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2614 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2615 : Integer.Sparse Key := [(key2078, 2), (key2082, -2), (key2275, -2), (key2289, 2), (key2328, 2), (key2333, -2)]

def row2616 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2617 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2618 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2619 : Integer.Sparse Key := [(key1998, 6), (key2000, -6), (key2267, -6), (key2292, 6), (key2340, 6), (key2349, -6)]

def row2620 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2621 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2622 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2623 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2624 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2625 : Integer.Sparse Key := [(key1998, -2), (key2000, 2), (key2267, 2), (key2292, -2), (key2340, -2), (key2349, 2)]

def row2626 : Integer.Sparse Key := [(key1998, -6), (key2000, 6), (key2267, 6), (key2292, -6), (key2340, -6), (key2349, 6)]

def row2627 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2628 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2629 : Integer.Sparse Key := [(key1998, 2), (key2000, -2), (key2267, -2), (key2292, 2), (key2340, 2), (key2349, -2)]

def row2630 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2631 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2632 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2633 : Integer.Sparse Key := [(key2006, 6), (key2007, -6), (key2299, -6), (key2313, 6), (key2340, 6), (key2349, -6)]

def row2634 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2635 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2636 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2637 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2638 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2639 : Integer.Sparse Key := [(key2006, -2), (key2007, 2), (key2299, 2), (key2313, -2), (key2340, -2), (key2349, 2)]

def row2640 : Integer.Sparse Key := [(key2006, -6), (key2007, 6), (key2299, 6), (key2313, -6), (key2340, -6), (key2349, 6)]

def row2641 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2642 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2643 : Integer.Sparse Key := [(key2006, 2), (key2007, -2), (key2299, -2), (key2313, 2), (key2340, 2), (key2349, -2)]

def row2644 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2645 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2646 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2647 : Integer.Sparse Key := [(key2092, 6), (key2095, -6), (key2194, -6), (key2200, 6), (key2305, 6), (key2310, -6)]

def row2648 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2649 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2650 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2651 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2652 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2653 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2194, 2), (key2200, -2), (key2305, -2), (key2310, 2)]

def row2654 : Integer.Sparse Key := [(key2092, -6), (key2095, 6), (key2194, 6), (key2200, -6), (key2305, -6), (key2310, 6)]

def row2655 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2656 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2657 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2194, -2), (key2200, 2), (key2305, 2), (key2310, -2)]

def row2658 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2659 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2660 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -2), (key836, -2), (key839, 2)]

def row2661 : Integer.Sparse Key := [(key776, 6), (key778, -6), (key801, -6), (key811, 6), (key836, 6), (key839, -6)]

def row2662 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2663 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2664 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 8), (key836, -4), (key839, -2)]

def row2665 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2666 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2667 : Integer.Sparse Key := [(key776, -2), (key778, 2), (key801, 2), (key811, -8), (key836, 4), (key839, 2)]

def row2668 : Integer.Sparse Key := [(key776, -6), (key778, 6), (key801, 6), (key811, -6), (key836, -6), (key839, 6)]

def row2669 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2670 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2671 : Integer.Sparse Key := [(key776, 2), (key778, -2), (key801, -2), (key811, 2), (key836, 2), (key839, -2)]

def row2672 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2673 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2674 : Integer.Sparse Key := [(key2407, -2), (key2410, 2), (key2441, -2), (key2445, 2), (key2473, 2), (key2483, -2), (key2507, 2), (key2526, -2), (key2539, -2), (key2544, 2), (key2557, -2), (key2565, 2)]

def row2675 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2676 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2677 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2473, -2), (key2483, 2), (key2507, -2), (key2526, 2), (key2539, 2), (key2544, -2), (key2557, 2), (key2565, -2)]

def row2678 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2679 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2680 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, 2), (key2445, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2970, -4), (key2991, 2), (key2993, 2)]

def row2681 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

def row2682 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -2), (key2407, -1), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2544, -1), (key2555, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 2), (key2848, 1), (key2882, -1), (key2912, 2), (key2970, 1), (key2991, 1), (key2993, -2), (key3003, 2)]

def row2683 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2684 : Integer.Sparse Key := [(key2382, 1), (key2393, -2), (key2410, 1), (key2441, -1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 2), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2685 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2407, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2592, 1), (key2595, -1), (key2602, 1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2686 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2410, 1), (key2445, 1), (key2483, -1), (key2526, -1), (key2557, 1), (key2565, -1), (key2595, -1), (key2602, 1), (key2771, -1), (key2848, 1), (key2882, -1), (key2912, 1), (key2933, -1), (key2970, 1), (key2993, -2), (key3003, 2)]

def row2687 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

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

def row2688 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

def row2689 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2441, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2774, 4), (key2882, -2), (key2891, -4), (key2912, 2), (key2934, 2), (key2993, -2), (key2996, -2), (key3003, 2)]

def row2690 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2691 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2934, -1), (key2970, -1), (key2991, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2692 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2693 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2694 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2592, -1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2695 : Integer.Sparse Key := [(key2771, 1), (key2774, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -1), (key2933, 1), (key2934, -1), (key2970, -1), (key2993, 1), (key2996, 1), (key3003, -1)]

def row2696 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2697 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2698 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2699 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2700 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2701 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2702 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2703 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2704 : Integer.Sparse Key := [(key1254, 4), (key1263, -4), (key1529, -4), (key1646, 4), (key1763, 4), (key1804, -4)]

def row2705 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2706 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2707 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2708 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2709 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2710 : Integer.Sparse Key := [(key1254, -2), (key1263, 2), (key1529, 2), (key1646, -2), (key1763, -2), (key1804, 2)]

def row2711 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2712 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2713 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 4), (key1646, -4), (key1763, -4), (key1804, 4)]

def row2714 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2715 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2716 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2717 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2718 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2719 : Integer.Sparse Key := [(key1254, 2), (key1263, -2), (key1529, -2), (key1646, 2), (key1763, 2), (key1804, -2)]

def row2720 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2722 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2390, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2)]

def row2723 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2724 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2725 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2406, -2), (key2411, -2), (key2437, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2)]

def row2726 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2727 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2728 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, 2), (key2889, 2), (key2966, -2), (key2968, -2)]

def row2729 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2730 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2731 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2732 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2733 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2734 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2766, 1), (key2772, 1), (key2887, -1), (key2889, -1), (key2929, -1), (key2931, -1), (key2966, 1), (key2968, 1)]

def row2735 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2736 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2737 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2598, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2887, -2), (key2889, -2), (key2929, -2), (key2931, -2), (key2966, 2), (key2968, 2)]

def row2738 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2739 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2740 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2741 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2742 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2743 : Integer.Sparse Key := [(key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -1), (key2772, -1), (key2887, 1), (key2889, 1), (key2929, 1), (key2931, 1), (key2966, -1), (key2968, -1)]

def row2744 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2745 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2746 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2747 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2748 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2749 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2750 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2751 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2752 : Integer.Sparse Key := [(key976, 4), (key984, -4), (key1090, -4), (key1169, 4), (key1183, 4), (key1220, -4)]

def row2753 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2754 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2755 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2756 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2757 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2758 : Integer.Sparse Key := [(key976, -2), (key984, 2), (key1090, 2), (key1169, -2), (key1183, -2), (key1220, 2)]

def row2759 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2760 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2761 : Integer.Sparse Key := [(key976, -4), (key984, 4), (key1090, 4), (key1169, -4), (key1183, -4), (key1220, 4)]

def row2762 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2763 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2764 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2765 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2766 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2767 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1090, -2), (key1169, 2), (key1183, 2), (key1220, -2)]

def row2768 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2769 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2770 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2771 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2772 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2773 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2774 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2775 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2776 : Integer.Sparse Key := [(key2377, 4), (key2389, -4), (key2405, -4), (key2436, 4), (key2479, 4), (key2502, -4)]

def row2777 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2778 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2779 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2780 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2781 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2782 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, 2), (key2436, -2), (key2479, -2), (key2502, 2)]

def row2783 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2784 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2785 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 4), (key2436, -4), (key2479, -4), (key2502, 4)]

def row2786 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2787 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2788 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2789 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2790 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2791 : Integer.Sparse Key := [(key2377, 2), (key2389, -2), (key2405, -2), (key2436, 2), (key2479, 2), (key2502, -2)]

def row2792 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2793 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2794 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2795 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2796 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2797 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2798 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2799 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2800 : Integer.Sparse Key := [(key1531, 2), (key1536, -2), (key1609, -2), (key1642, 2), (key1651, 2), (key1674, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1832, 2), (key1837, 2), (key1848, -2)]

def row2801 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2802 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2803 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2804 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2805 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2806 : Integer.Sparse Key := [(key1531, -1), (key1536, 1), (key1609, 1), (key1642, -1), (key1651, -1), (key1674, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1832, -1), (key1837, -1), (key1848, 1)]

def row2807 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

def row2808 : Integer.Sparse Key := [(key1531, -2), (key1536, 2), (key1609, 2), (key1642, -2), (key1651, -2), (key1674, 2), (key1765, -2), (key1768, 2), (key1806, 2), (key1832, -2), (key1837, -2), (key1848, 2)]

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

def row2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, 4), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2913 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2914 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2363, -2), (key2366, 6), (key2456, 4), (key2523, -4), (key2567, -4), (key2579, 4)]

def row2915 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2916 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2917 : Integer.Sparse Key := [(key2357, -2), (key2361, 6), (key2363, -4), (key2456, -4), (key2523, 4), (key2567, 4), (key2579, -4)]

def row2918 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, -4), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2919 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2920 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2366, -6), (key2452, -4), (key2458, -2), (key2461, 2), (key2519, 6), (key2523, 4), (key2567, -2), (key2579, -4)]

def row2921 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2922 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2923 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2924 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2925 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2926 : Integer.Sparse Key := [(key2361, -2), (key2366, 2), (key2452, 4), (key2456, -2), (key2458, -2), (key2461, 2), (key2517, -2), (key2519, -2), (key2523, -4), (key2528, 2), (key2530, 2), (key2560, 2)]

def row2927 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2928 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2929 : Integer.Sparse Key := [(key2357, 2), (key2361, -6), (key2363, 4), (key2456, 4), (key2517, 2), (key2519, -4), (key2528, -2), (key2530, -4), (key2560, 4)]

def row2930 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2931 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2932 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2933 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2934 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2935 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, 2), (key2456, -4), (key2517, 2), (key2519, 2), (key2528, -2), (key2530, 2), (key2560, -2)]

def row2936 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2937 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2938 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2939 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2940 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2941 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2942 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2943 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

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

def row2944 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

def row2945 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2946 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2947 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2948 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2949 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2950 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

def row2951 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2952 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2953 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

def row2954 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2955 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2956 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2957 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2958 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2959 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

def row2960 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2962 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2963 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2964 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2965 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2966 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2967 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2968 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

def row2969 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2970 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2971 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2972 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2973 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2974 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

def row2975 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2976 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2977 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

def row2978 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2979 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2980 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2981 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2982 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2983 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

def row2984 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2985 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2986 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row2987 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2988 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2989 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2990 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2991 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2992 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

def row2993 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2994 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2995 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2996 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2997 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2998 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

def row2999 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3000 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3001 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

def row3002 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3003 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3004 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3005 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3006 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3007 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

def row3008 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3009 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3010 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3011 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3012 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3013 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

def row3014 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3015 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3016 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

def row3017 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3018 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3019 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3020 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3021 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3022 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

def row3023 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3024 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3025 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

def row3026 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3027 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3028 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3029 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3030 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

def row3031 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

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

def nodeValue1015 : Sparse Master := [(Sum.inr 1015, (1 / 1))]

def nodeValue1016 : Sparse Master := [(Sum.inr 1016, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


