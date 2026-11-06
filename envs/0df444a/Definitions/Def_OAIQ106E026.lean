-- Prove2me | Definitions.Def_OAIQ106E026
-- name    : OAIQ106E026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:47:50.404542+00:00
-- url     : https://prove2.me/theorems/abbe93b9-8e83-47dc-8b9a-5fa7b6bf07d9
-- title:
--   Definitions bundle OAIQ106E026 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block2.rows6_6`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_4`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block2Row6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row6.lean), [`MutuallyUnbiased_GramEntries_Block2Row7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row7.lean), [`MutuallyUnbiased_GramEntries_Block2Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row8.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018`, `OAIQ106E021` and `OAIQ106E025` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_4_e` and `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_5_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E021
import Definitions.Def_OAIQ106E025

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_6 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6138, row6139, row6140, row6141, row6142, row6143, row6144, row6145, row6146, row6147, row6148, row6149, row6150, row6151, row6152, row6153, row6154, row6155, row6156, row6157, row6158, row6159, row6160, row6161, row6162, row6163, row6164, row6165, row6166, row6167, row6168, row6169, row6170, row6171, row6172, row6173, row6174, row6175, row6176, row6177]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row6178, row6179, row5174, row5175, row6180, row6181, row5176, row5177, row5182, row5183, row6182, row6183, row5184, row5185, row6184, row6185, row6186, row6187, row6188, row6189, row6190, row6191, row6192, row6193, row6194, row6195, row6196, row6197]

def rows7_3 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6278, row6279, row6280, row6281, row6282, row6283, row6284, row6285, row6286, row6287, row6288, row6289, row6290, row6291, row6292, row6293, row6294, row6295, row6296, row6297, row6298, row6299, row6300, row6301, row6302, row6303, row6304, row6305, row6306, row6307, row6308, row6309, row6310, row6311, row6312, row6313, row6314, row6315, row6316, row6317]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6478, row6479, row6480, row6481, row6482, row6483, row6484, row6485, row6486, row6487, row6488, row6489, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row6490, row6491, row5686, row5687, row6492, row6493, row6494, row6495, row5692, row5693, row6496, row6497, row5696, row5697]

def rows8_1 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6498, row6499, row6500, row6501, row6502, row6503, row6504, row6505, row6506, row6507, row6508, row6509, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row6510, row6511, row5726, row5727, row6512, row6513, row6514, row6515, row5732, row5733, row6516, row6517, row5736, row5737]

def rows8_2 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6518, row6519, row6520, row6521, row6522, row6523, row6524, row6525, row6526, row6527, row6528, row6529, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row6530, row6531, row5766, row5767, row6532, row6533, row6534, row6535, row5772, row5773, row6536, row6537, row5776, row5777]

def rows8_3 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6538, row6539, row6540, row6541, row6542, row6543, row6544, row6545, row6546, row6547, row6548, row6549, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row6550, row6551, row5806, row5807, row6552, row6553, row6554, row6555, row5812, row5813, row6556, row6557, row5816, row5817]

def rows8_4 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6558, row6559, row6560, row6561, row6562, row6563, row6564, row6565, row6566, row6567, row6568, row6569, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row6570, row6571, row5846, row5847, row6572, row6573, row6574, row6575, row5852, row5853, row6576, row6577, row5856, row5857]

def rows8_5 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6578, row6579, row6580, row6581, row6582, row6583, row6584, row6585, row6586, row6587, row6588, row6589, row5870, row5871, row5872, row5873, row5874, row5875, row5876, row5877, row5878, row5879, row5880, row5881, row5882, row5883, row6590, row6591, row5886, row5887, row6592, row6593, row6594, row6595, row5892, row5893, row6596, row6597, row5896, row5897]

end MUB6.Certificate.GramEntries.Block2

end OAI
end


