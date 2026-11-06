-- Prove2me | Definitions.Def_OAIQ106E036
-- name    : OAIQ106E036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T01:02:21.735539+00:00
-- url     : https://prove2.me/theorems/0a81ae5e-91da-4e6f-bc5d-342884246415
-- title:
--   Definitions bundle OAIQ106E036 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block4.rows15_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_4`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_5`, `OAI.MUB6.Certificate.GramEntries.Block4.rows6_6`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block4Row15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row15.lean), [`MutuallyUnbiased_GramEntries_Block4Row6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row6.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018`, `OAIQ106E032` and `OAIQ106E035` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_4_e` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_5_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E035

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_9 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15879, row15880, row15881, row15882, row15883, row15884, row15885, row15886, row15887, row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row15888, row15889, row15890, row15891, row15892, row15893, row14538, row14539, row14540, row14541, row14542, row14543, row15894, row15895, row15896, row14556, row14557, row14558]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613, row13614, row13615, row13616, row13617, row13618, row13619, row13620, row13621, row13622, row13623, row13624, row13625, row13626, row13627, row13628]

def rows6_1 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649, row13650, row13651, row13652, row13653, row13654, row13655, row13656, row13657, row13658, row13659, row13660, row13661, row13662, row13663, row13664]

def rows6_2 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685, row13686, row13687, row13688, row13689, row13690, row13691, row13692, row13693, row13694, row13695, row13696, row13697, row13698, row13699, row13700]

def rows6_3 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721, row13722, row13723, row13724, row13725, row13726, row13727, row13728, row13729, row13730, row13731, row13732, row13733, row13734, row13735, row13736]

def rows6_4 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757, row13758, row13759, row13760, row13761, row13762, row13763, row13764, row13765, row13766, row13767, row13768, row13769, row13770, row13771, row13772]

def rows6_5 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793, row13794, row13795, row13796, row13797, row13798, row13799, row13800, row13801, row13802, row13803, row13804, row13805, row13806, row13807, row13808]

def rows6_6 : Fin GramFunctions.Block4.form6.size → Integer.Sparse Key := ![row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829, row13830, row13831, row13832, row13833, row13834, row13835, row13836, row13837, row13838, row13839, row13840, row13841, row13842, row13843, row13844]

end MUB6.Certificate.GramEntries.Block4

end OAI
end


