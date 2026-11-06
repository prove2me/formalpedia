-- Prove2me | Definitions.Def_OAIQ106E014
-- name    : OAIQ106E014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T23:54:42.655736+00:00
-- url     : https://prove2.me/theorems/9d0fe23f-2b27-4329-9740-35f71f01c854
-- title:
--   Definitions bundle OAIQ106E014 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 79 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block0.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows1_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows1_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_2`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_3`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows10_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_11`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows11_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows12_0` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block0Row0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block0Row0.lean), [`MutuallyUnbiased_GramEntries_Block0Row1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block0Row1.lean), [`MutuallyUnbiased_GramEntries_Block0Row2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block0Row2.lean), [`MutuallyUnbiased_GramEntries_Block0Row3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block0Row3.lean), [`MutuallyUnbiased_GramEntries_Block0Row4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block0Row4.lean), [`MutuallyUnbiased_GramEntries_Block1Row0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row0.lean), [`MutuallyUnbiased_GramEntries_Block1Row10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row10.lean), [`MutuallyUnbiased_GramEntries_Block1Row11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row11.lean), [`MutuallyUnbiased_GramEntries_Block1Row12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row12.lean), [`MutuallyUnbiased_GramEntries_Block1Row13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row13.lean), [`MutuallyUnbiased_GramEntries_Block1Row14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row14.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E196` and `OAIQ106E013` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E013

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block0.form0.size → Integer.Sparse Key := ![row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83]

def rows1_1 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row126, row127, row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167]

def rows2_1 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209]

def rows2_2 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row252, row253, row254, row255, row256, row257, row258, row259, row260, row261, row262, row263, row264, row265, row266, row267, row268, row269, row270, row271, row272, row273, row274, row275, row276, row277, row278, row279, row280, row281, row282, row283, row284, row285, row286, row287, row288, row289, row290, row291, row292, row293]

def rows3_1 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row294, row295, row296, row297, row298, row299, row300, row301, row302, row303, row304, row305, row306, row307, row308, row309, row310, row311, row312, row313, row314, row315, row316, row317, row318, row319, row320, row321, row322, row323, row324, row325, row326, row327, row328, row329, row330, row331, row332, row333, row334, row335]

def rows3_2 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row336, row337, row338, row339, row340, row341, row342, row343, row344, row345, row346, row347, row348, row349, row350, row351, row352, row353, row354, row355, row356, row357, row358, row359, row360, row361, row362, row363, row364, row365, row366, row367, row368, row369, row370, row371, row372, row373, row374, row375, row376, row377]

def rows3_3 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row378, row379, row380, row381, row382, row383, row384, row385, row386, row387, row388, row389, row390, row391, row392, row393, row394, row395, row396, row397, row398, row399, row400, row401, row402, row403, row404, row405, row406, row407, row408, row409, row410, row411, row412, row413, row414, row415, row416, row417, row418, row419]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row420, row421, row422, row423, row424, row425, row426, row427, row428, row429, row430, row431, row432, row433, row434, row435, row436, row437, row438, row439, row440, row441, row442, row443, row444, row445, row446, row447, row448, row449, row450, row451, row452, row453, row454, row455, row456, row457, row458, row459, row460, row461]

def rows4_1 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row462, row463, row464, row465, row466, row467, row468, row469, row470, row471, row472, row473, row474, row475, row476, row477, row478, row479, row480, row481, row482, row483, row484, row485, row486, row487, row488, row489, row490, row491, row492, row493, row494, row495, row496, row497, row498, row499, row500, row501, row502, row503]

def rows4_2 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row504, row505, row506, row507, row508, row509, row510, row511, row512, row513, row514, row515, row516, row517, row518, row519, row520, row521, row522, row523, row524, row525, row526, row527, row528, row529, row530, row531, row532, row533, row534, row535, row536, row537, row538, row539, row540, row541, row542, row543, row544, row545]

def rows4_3 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row546, row547, row548, row549, row550, row551, row552, row553, row554, row555, row556, row557, row558, row559, row560, row561, row562, row563, row564, row565, row566, row567, row568, row569, row570, row571, row572, row573, row574, row575, row576, row577, row578, row579, row580, row581, row582, row583, row584, row585, row586, row587]

def rows4_4 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row588, row589, row590, row591, row592, row593, row594, row595, row596, row597, row598, row599, row600, row601, row602, row603, row604, row605, row606, row607, row608, row609, row610, row611, row612, row613, row614, row615, row616, row617, row618, row619, row620, row621, row622, row623, row624, row625, row626, row627, row628, row629]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block1.form0.size → Integer.Sparse Key := ![row630, row631, row632, row633, row634, row635, row636, row637, row638, row639, row640, row641, row642, row643, row644, row645, row646, row647, row648, row649, row650, row651, row652, row653, row654, row655, row656, row657, row658, row659]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1764, row1765, row1766, row1767, row1768, row1769, row1770, row1771, row1772, row1773, row1774, row1775, row1776, row1777]

def rows10_1 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1778, row1779, row1780, row1781, row1782, row1783, row1784, row1785, row1786, row1787, row1788, row1789, row1790, row1791]

def rows10_2 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1792, row1793, row1794, row1795, row1796, row1797, row1798, row1799, row1800, row1801, row1802, row1803, row1804, row1805]

def rows10_3 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1806, row1807, row1808, row1809, row1810, row1811, row1812, row1813, row1814, row1815, row1816, row1817, row1818, row1819]

def rows10_4 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1820, row1821, row1822, row1823, row1824, row1825, row1826, row1827, row1828, row1829, row1830, row1831, row1832, row1833]

def rows10_5 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1834, row1835, row1836, row1837, row1838, row1839, row1840, row1841, row1842, row1843, row1844, row1845, row1846, row1847]

def rows10_6 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1848, row1849, row1850, row1851, row1852, row1853, row1854, row1855, row1856, row1857, row1858, row1859, row1860, row1861]

def rows10_7 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1862, row1863, row1864, row1865, row1866, row1867, row1868, row1869, row1870, row1871, row1872, row1873, row1874, row1875]

def rows10_8 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1876, row1877, row1878, row1879, row1880, row1881, row1882, row1883, row1884, row1885, row1886, row1887, row1888, row1889]

def rows10_9 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1890, row1891, row1892, row1893, row1894, row1895, row1896, row1897, row1898, row1899, row1900, row1901, row1902, row1903]

def rows10_10 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1904, row1905, row1906, row1907, row1908, row1909, row1910, row1911, row1912, row1913, row1914, row1915, row1916, row1917]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1918, row1919, row1920, row1921, row1922, row1923, row1924, row1925, row1926, row1927, row1928, row1929, row1930, row1931]

def rows11_1 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1932, row1933, row1934, row1935, row1936, row1937, row1938, row1939, row1940, row1941, row1942, row1943, row1944, row1945]

def rows11_2 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1946, row1947, row1948, row1949, row1950, row1951, row1952, row1953, row1954, row1955, row1956, row1957, row1958, row1959]

def rows11_3 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1960, row1961, row1962, row1963, row1964, row1965, row1966, row1967, row1968, row1969, row1970, row1971, row1972, row1973]

def rows11_4 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1974, row1975, row1976, row1977, row1978, row1979, row1980, row1981, row1982, row1983, row1984, row1985, row1986, row1987]

def rows11_5 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1988, row1989, row1990, row1991, row1992, row1993, row1994, row1995, row1996, row1997, row1998, row1999, row2000, row2001]

def rows11_6 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2002, row2003, row2004, row2005, row2006, row2007, row2008, row2009, row2010, row2011, row2012, row2013, row2014, row2015]

def rows11_7 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2016, row2017, row2018, row2019, row2020, row2021, row2022, row2023, row2024, row2025, row2026, row2027, row2028, row2029]

def rows11_8 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2030, row2031, row2032, row2033, row2034, row2035, row2036, row2037, row2038, row2039, row2040, row2041, row2042, row2043]

def rows11_9 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2044, row2045, row2046, row2047, row2048, row2049, row2050, row2051, row2052, row2053, row2054, row2055, row2056, row2057]

def rows11_10 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2058, row2059, row2060, row2061, row2062, row2063, row2064, row2065, row2066, row2067, row2068, row2069, row2070, row2071]

def rows11_11 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2072, row2073, row2074, row2075, row2076, row2077, row2078, row2079, row2080, row2081, row2082, row2083, row2084, row2085]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2086, row2087, row2088, row2089, row2090, row2091, row2092, row2093, row2094, row2095, row2096, row2097, row2098, row2099, row2100, row2101, row2102, row2103, row2104, row2105, row2106, row2107, row2108, row2109, row2110, row2111, row2112, row2113, row2114, row2115]

def rows12_1 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2116, row2117, row2118, row2119, row2120, row2121, row2122, row2123, row2124, row2125, row2126, row2127, row2128, row2129, row2130, row2131, row2132, row2133, row2134, row2135, row2136, row2137, row2138, row2139, row2140, row2141, row2142, row2143, row2144, row2145]

def rows12_2 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2146, row2147, row2148, row2149, row2150, row2151, row2152, row2153, row2154, row2155, row2156, row2157, row2158, row2159, row2160, row2161, row2162, row2163, row2164, row2165, row2166, row2167, row2168, row2169, row2170, row2171, row2172, row2173, row2174, row2175]

def rows12_3 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2176, row2177, row2178, row2179, row2180, row2181, row2182, row2183, row2184, row2185, row2186, row2187, row2188, row2189, row2190, row2191, row2192, row2193, row2194, row2195, row2196, row2197, row2198, row2199, row2200, row2201, row2202, row2203, row2204, row2205]

def rows12_4 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2206, row2207, row2208, row2209, row2210, row2211, row2212, row2213, row2214, row2215, row2216, row2217, row2218, row2219, row2220, row2221, row2222, row2223, row2224, row2225, row2226, row2227, row2228, row2229, row2230, row2231, row2232, row2233, row2234, row2235]

def rows12_5 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2236, row2237, row2238, row2239, row2240, row2241, row2242, row2243, row2244, row2245, row2246, row2247, row2248, row2249, row2250, row2251, row2252, row2253, row2254, row2255, row2256, row2257, row2258, row2259, row2260, row2261, row2262, row2263, row2264, row2265]

def rows12_6 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2266, row2267, row2268, row2269, row2270, row2271, row2272, row2273, row2274, row2275, row2276, row2277, row2278, row2279, row2280, row2281, row2282, row2283, row2284, row2285, row2286, row2287, row2288, row2289, row2290, row2291, row2292, row2293, row2294, row2295]

def rows12_7 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2296, row2297, row2298, row2299, row2300, row2301, row2302, row2303, row2304, row2305, row2306, row2307, row2308, row2309, row2310, row2311, row2312, row2313, row2314, row2315, row2316, row2317, row2318, row2319, row2320, row2321, row2322, row2323, row2324, row2325]

def rows12_8 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2326, row2327, row2328, row2329, row2330, row2331, row2332, row2333, row2334, row2335, row2336, row2337, row2338, row2339, row2340, row2341, row2342, row2343, row2344, row2345, row2346, row2347, row2348, row2349, row2350, row2351, row2352, row2353, row2354, row2355]

def rows12_9 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2356, row2357, row2358, row2359, row2360, row2361, row2362, row2363, row2364, row2365, row2366, row2367, row2368, row2369, row2370, row2371, row2372, row2373, row2374, row2375, row2376, row2377, row2378, row2379, row2380, row2381, row2382, row2383, row2384, row2385]

def rows12_10 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2386, row2387, row2388, row2389, row2390, row2391, row2392, row2393, row2394, row2395, row2396, row2397, row2398, row2399, row2400, row2401, row2402, row2403, row2404, row2405, row2406, row2407, row2408, row2409, row2410, row2411, row2412, row2413, row2414, row2415]

def rows12_11 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2416, row2417, row2418, row2419, row2420, row2421, row2422, row2423, row2424, row2425, row2426, row2427, row2428, row2429, row2430, row2431, row2432, row2433, row2434, row2435, row2436, row2437, row2438, row2439, row2440, row2441, row2442, row2443, row2444, row2445]

def rows12_12 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2446, row2447, row2448, row2449, row2450, row2451, row2452, row2453, row2454, row2455, row2456, row2457, row2458, row2459, row2460, row2461, row2462, row2463, row2464, row2465, row2466, row2467, row2468, row2469, row2470, row2471, row2472, row2473, row2474, row2475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2476, row2477, row2478, row2479, row2480, row2481, row2482, row2483, row2484, row2485, row2486, row2487, row2488, row2489]

def rows13_1 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2490, row2491, row2492, row2493, row2494, row2495, row2496, row2497, row2498, row2499, row2500, row2501, row2502, row2503]

def rows13_2 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2504, row2505, row2506, row2507, row2508, row2509, row2510, row2511, row2512, row2513, row2514, row2515, row2516, row2517]

def rows13_3 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2518, row2519, row2520, row2521, row2522, row2523, row2524, row2525, row2526, row2527, row2528, row2529, row2530, row2531]

def rows13_4 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2532, row2533, row2534, row2535, row2536, row2537, row2538, row2539, row2540, row2541, row2542, row2543, row2544, row2545]

def rows13_5 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2546, row2547, row2548, row2549, row2550, row2551, row2552, row2553, row2554, row2555, row2556, row2557, row2558, row2559]

def rows13_6 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2560, row2561, row2562, row2563, row2564, row2565, row2566, row2567, row2568, row2569, row2570, row2571, row2572, row2573]

def rows13_7 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2574, row2575, row2576, row2577, row2578, row2579, row2580, row2581, row2582, row2583, row2584, row2585, row2586, row2587]

def rows13_8 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2588, row2589, row2590, row2591, row2592, row2593, row2594, row2595, row2596, row2597, row2598, row2599, row2600, row2601]

def rows13_9 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2602, row2603, row2604, row2605, row2606, row2607, row2608, row2609, row2610, row2611, row2612, row2613, row2614, row2615]

def rows13_10 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2616, row2617, row2618, row2619, row2620, row2621, row2622, row2623, row2624, row2625, row2626, row2627, row2628, row2629]

def rows13_11 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2630, row2631, row2632, row2633, row2634, row2635, row2636, row2637, row2638, row2639, row2640, row2641, row2642, row2643]

def rows13_12 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2644, row2645, row2646, row2647, row2648, row2649, row2650, row2651, row2652, row2653, row2654, row2655, row2656, row2657]

def rows13_13 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2658, row2659, row2660, row2661, row2662, row2663, row2664, row2665, row2666, row2667, row2668, row2669, row2670, row2671]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2672, row2673, row2674, row2675, row2676, row2677, row2678, row2679, row2680, row2681, row2682, row2683, row2684, row2685, row2686, row2687, row2688, row2689, row2690, row2691, row2692, row2693, row2694, row2695]

def rows14_1 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2696, row2697, row2698, row2699, row2700, row2701, row2702, row2703, row2704, row2705, row2706, row2707, row2708, row2709, row2710, row2711, row2712, row2713, row2714, row2715, row2716, row2717, row2718, row2719]

def rows14_2 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2720, row2721, row2722, row2723, row2724, row2725, row2726, row2727, row2728, row2729, row2730, row2731, row2732, row2733, row2734, row2735, row2736, row2737, row2738, row2739, row2740, row2741, row2742, row2743]

def rows14_3 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2744, row2745, row2746, row2747, row2748, row2749, row2750, row2751, row2752, row2753, row2754, row2755, row2756, row2757, row2758, row2759, row2760, row2761, row2762, row2763, row2764, row2765, row2766, row2767]

def rows14_4 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2768, row2769, row2770, row2771, row2772, row2773, row2774, row2775, row2776, row2777, row2778, row2779, row2780, row2781, row2782, row2783, row2784, row2785, row2786, row2787, row2788, row2789, row2790, row2791]

def rows14_5 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2792, row2793, row2794, row2795, row2796, row2797, row2798, row2799, row2800, row2801, row2802, row2803, row2804, row2805, row2806, row2807, row2808, row2809, row2810, row2811, row2812, row2813, row2814, row2815]

def rows14_6 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2816, row2817, row2818, row2819, row2820, row2821, row2822, row2823, row2824, row2825, row2826, row2827, row2828, row2829, row2830, row2831, row2832, row2833, row2834, row2835, row2836, row2837, row2838, row2839]

def rows14_7 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2840, row2841, row2842, row2843, row2844, row2845, row2846, row2847, row2848, row2849, row2850, row2851, row2852, row2853, row2854, row2855, row2856, row2857, row2858, row2859, row2860, row2861, row2862, row2863]

def rows14_10 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2912, row2913, row2914, row2915, row2916, row2917, row2918, row2919, row2920, row2921, row2922, row2923, row2924, row2925, row2926, row2927, row2928, row2929, row2930, row2931, row2932, row2933, row2934, row2935]

def rows14_11 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2936, row2937, row2938, row2939, row2940, row2941, row2942, row2943, row2944, row2945, row2946, row2947, row2948, row2949, row2950, row2951, row2952, row2953, row2954, row2955, row2956, row2957, row2958, row2959]

def rows14_12 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2960, row2961, row2962, row2963, row2964, row2965, row2966, row2967, row2968, row2969, row2970, row2971, row2972, row2973, row2974, row2975, row2976, row2977, row2978, row2979, row2980, row2981, row2982, row2983]

def rows14_13 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2984, row2985, row2986, row2987, row2988, row2989, row2990, row2991, row2992, row2993, row2994, row2995, row2996, row2997, row2998, row2999, row3000, row3001, row3002, row3003, row3004, row3005, row3006, row3007]

def rows14_14 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row3008, row3009, row3010, row3011, row3012, row3013, row3014, row3015, row3016, row3017, row3018, row3019, row3020, row3021, row3022, row3023, row3024, row3025, row3026, row3027, row3028, row3029, row3030, row3031]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


