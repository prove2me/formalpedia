-- Prove2me | Definitions.Def_OAIQ106E041
-- name    : OAIQ106E041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T01:06:37.420665+00:00
-- url     : https://prove2.me/theorems/6eb4e3c5-1589-403e-a577-5e2e362d0012
-- title:
--   Definitions bundle OAIQ106E041 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 60 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.rows11_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_4`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_5`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_6`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_7`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_9`, `OAI.MUB6.Certificate.GramEntries.Block5.rows1_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows1_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows2_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows4_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows4_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows4_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows4_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows4_4`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_4`, `OAI.MUB6.Certificate.GramEntries.Block5.rows5_5`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_4`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_5`, `OAI.MUB6.Certificate.GramEntries.Block5.rows6_6`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_0`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_1`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_2`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_4`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_5`, `OAI.MUB6.Certificate.GramEntries.Block5.rows7_6` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block5Row1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row1.lean), [`MutuallyUnbiased_GramEntries_Block5Row11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row11.lean), [`MutuallyUnbiased_GramEntries_Block5Row2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row2.lean), [`MutuallyUnbiased_GramEntries_Block5Row3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row3.lean), [`MutuallyUnbiased_GramEntries_Block5Row4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row4.lean), [`MutuallyUnbiased_GramEntries_Block5Row5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row5.lean), [`MutuallyUnbiased_GramEntries_Block5Row6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row6.lean), [`MutuallyUnbiased_GramEntries_Block5Row7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row7.lean), [`MutuallyUnbiased_GramEntries_Block5Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row8.lean), [`MutuallyUnbiased_GramEntries_Block5Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row9.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E039` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval2_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E039

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18449, row18450, row18451, row18452, row18453]

def rows1_1 : Fin GramFunctions.Block5.form1.size → Integer.Sparse Key := ![row18454, row18455, row18456, row18457, row18458]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_2 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19724, row19725, row19726, row19727, row19728, row19729, row19730, row19731, row19732, row19733, row19734, row19735, row19736, row19737, row19738, row19739, row19740, row19741, row19742, row19743, row19744, row19745, row19746, row19747, row19748, row19749, row19750, row19751, row19752, row19753, row19754, row19755, row19756, row19757, row19758, row19759, row19760, row19761, row19762, row19763, row19764, row19765, row19766, row19767, row19768, row19769, row19770, row19771, row19772, row19773, row19774, row19775, row19776, row19777, row19778, row19779, row19780, row19781, row19782, row19783]

def rows11_4 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19844, row19845, row19846, row19847, row19848, row19849, row19850, row19851, row19852, row19853, row19854, row19855, row19856, row19857, row19858, row19859, row19860, row19861, row19862, row19863, row19864, row19865, row19866, row19867, row19868, row19869, row19870, row19871, row19872, row19873, row19874, row19875, row19876, row19877, row19878, row19879, row19880, row19881, row19882, row19883, row19884, row19885, row19886, row19887, row19888, row19889, row19890, row19891, row19892, row19893, row19894, row19895, row19896, row19897, row19898, row19899, row19900, row19901, row19902, row19903]

def rows11_5 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19904, row19905, row19906, row19907, row19908, row19909, row19910, row19911, row19912, row19913, row19914, row19915, row19916, row19917, row19918, row19919, row19920, row19921, row19922, row19923, row19924, row19925, row19926, row19927, row19928, row19929, row19930, row19931, row19932, row19933, row19934, row19935, row19936, row19937, row19938, row19939, row19940, row19941, row19942, row19943, row19944, row19945, row19946, row19947, row19948, row19949, row19950, row19951, row19952, row19953, row19954, row19955, row19956, row19957, row19958, row19959, row19960, row19961, row19962, row19963]

def rows11_6 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19964, row19965, row19966, row19967, row19968, row19969, row19970, row19971, row19972, row19973, row19974, row19975, row19976, row19977, row19978, row19979, row19980, row19981, row19982, row19983, row19984, row19985, row19986, row19987, row19988, row19989, row19990, row19991, row19992, row19993, row19994, row19995, row19996, row19997, row19998, row19999, row20000, row20001, row20002, row20003, row20004, row20005, row20006, row20007, row20008, row20009, row20010, row20011, row20012, row20013, row20014, row20015, row20016, row20017, row20018, row20019, row20020, row20021, row20022, row20023]

def rows11_7 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20024, row20025, row20026, row20027, row20028, row20029, row20030, row20031, row20032, row20033, row20034, row20035, row20036, row20037, row20038, row20039, row20040, row20041, row20042, row20043, row20044, row20045, row20046, row20047, row20048, row20049, row20050, row20051, row20052, row20053, row20054, row20055, row20056, row20057, row20058, row20059, row20060, row20061, row20062, row20063, row20064, row20065, row20066, row20067, row20068, row20069, row20070, row20071, row20072, row20073, row20074, row20075, row20076, row20077, row20078, row20079, row20080, row20081, row20082, row20083]

def rows11_9 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20144, row20145, row20146, row20147, row20148, row20149, row20150, row20151, row20152, row20153, row20154, row20155, row20156, row20157, row20158, row20159, row20160, row20161, row20162, row20163, row20164, row20165, row20166, row20167, row20168, row20169, row20170, row20171, row20172, row20173, row20174, row20175, row20176, row20177, row20178, row20179, row20180, row20181, row20182, row20183, row20184, row20185, row20186, row20187, row20188, row20189, row20190, row20191, row20192, row20193, row20194, row20195, row20196, row20197, row20198, row20199, row20200, row20201, row20202, row20203]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18459, row18460, row18461, row18462, row18463, row18464, row18465, row18466, row18467, row18468, row18469, row18470, row18471, row18472, row18473, row18474, row18475, row18476, row18477, row18478, row18479, row18480, row18481, row18482, row18483, row18484, row18485, row18486, row18487, row18488, row18489, row18490, row18491, row18492, row18493, row18494, row18495, row18496, row18497, row18498, row18499, row18500, row18501, row18502, row18503, row18504, row18505, row18506, row18507, row18508, row18509, row18510, row18511, row18512, row18513, row18514, row18515, row18516, row18517, row18518]

def rows2_1 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18519, row18520, row18521, row18522, row18523, row18524, row18525, row18526, row18527, row18528, row18529, row18530, row18531, row18532, row18533, row18534, row18535, row18536, row18537, row18538, row18539, row18540, row18541, row18542, row18543, row18544, row18545, row18546, row18547, row18548, row18549, row18550, row18551, row18552, row18553, row18554, row18555, row18556, row18557, row18558, row18559, row18560, row18561, row18562, row18563, row18564, row18565, row18566, row18567, row18568, row18569, row18570, row18571, row18572, row18573, row18574, row18575, row18576, row18577, row18578]

def rows2_2 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18579, row18580, row18581, row18582, row18583, row18584, row18585, row18586, row18587, row18588, row18589, row18590, row18591, row18592, row18593, row18594, row18595, row18596, row18597, row18598, row18599, row18600, row18601, row18602, row18603, row18604, row18605, row18606, row18607, row18608, row18609, row18610, row18611, row18612, row18613, row18614, row18615, row18616, row18617, row18618, row18619, row18620, row18621, row18622, row18623, row18624, row18625, row18626, row18627, row18628, row18629, row18630, row18631, row18632, row18633, row18634, row18635, row18636, row18637, row18638]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18639, row18640, row18641, row18642, row18643]

def rows3_1 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18644, row18645, row18646, row18647, row18648]

def rows3_2 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18649, row18650, row18651, row18652, row18653]

def rows3_3 : Fin GramFunctions.Block5.form3.size → Integer.Sparse Key := ![row18654, row18655, row18656, row18657, row18658]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18659, row18660, row18661, row18662, row18663, row18664, row18665, row18666, row18667, row18668, row18669, row18670, row18671, row18672, row18673, row18674, row18675, row18676, row18677, row18678]

def rows4_1 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18679, row18680, row18681, row18682, row18683, row18684, row18685, row18686, row18687, row18688, row18689, row18690, row18691, row18692, row18693, row18694, row18695, row18696, row18697, row18698]

def rows4_2 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18699, row18700, row18701, row18702, row18703, row18704, row18705, row18706, row18707, row18708, row18709, row18710, row18711, row18712, row18713, row18714, row18715, row18716, row18717, row18718]

def rows4_3 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18719, row18720, row18721, row18722, row18723, row18724, row18725, row18726, row18727, row18728, row18729, row18730, row18731, row18732, row18733, row18734, row18735, row18736, row18737, row18738]

def rows4_4 : Fin GramFunctions.Block5.form4.size → Integer.Sparse Key := ![row18739, row18740, row18741, row18742, row18743, row18744, row18745, row18746, row18747, row18748, row18749, row18750, row18751, row18752, row18753, row18754, row18755, row18756, row18757, row18758]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18759, row18760, row18761, row18762, row18763, row18764, row18765, row18766, row18767, row18768, row18769, row18770, row18771, row18772, row18773, row18774, row18775, row18776, row18777, row18778, row18779, row18780, row18781, row18782, row18783, row18784, row18785, row18786, row18787, row18788]

def rows5_1 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18789, row18790, row18791, row18792, row18793, row18794, row18795, row18796, row18797, row18798, row18799, row18800, row18801, row18802, row18803, row18804, row18805, row18806, row18807, row18808, row18809, row18810, row18811, row18812, row18813, row18814, row18815, row18816, row18817, row18818]

def rows5_2 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18819, row18820, row18821, row18822, row18823, row18824, row18825, row18826, row18827, row18828, row18829, row18830, row18831, row18832, row18833, row18834, row18835, row18836, row18837, row18838, row18839, row18840, row18841, row18842, row18843, row18844, row18845, row18846, row18847, row18848]

def rows5_3 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18849, row18850, row18851, row18852, row18853, row18854, row18855, row18856, row18857, row18858, row18859, row18860, row18861, row18862, row18863, row18864, row18865, row18866, row18867, row18868, row18869, row18870, row18871, row18872, row18873, row18874, row18875, row18876, row18877, row18878]

def rows5_4 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18879, row18880, row18881, row18882, row18883, row18884, row18885, row18886, row18887, row18888, row18889, row18890, row18891, row18892, row18893, row18894, row18895, row18896, row18897, row18898, row18899, row18900, row18901, row18902, row18903, row18904, row18905, row18906, row18907, row18908]

def rows5_5 : Fin GramFunctions.Block5.form5.size → Integer.Sparse Key := ![row18909, row18910, row18911, row18912, row18913, row18914, row18915, row18916, row18917, row18918, row18919, row18920, row18921, row18922, row18923, row18924, row18925, row18926, row18927, row18928, row18929, row18930, row18931, row18932, row18933, row18934, row18935, row18936, row18937, row18938]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18939, row18940, row18941, row18942, row18943, row18944, row18945, row18946, row18947, row18948, row18949, row18950, row18951, row18952, row18953, row18954, row18955, row18956, row18957, row18958]

def rows6_1 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18959, row18960, row18961, row18962, row18963, row18964, row18965, row18966, row18967, row18968, row18969, row18970, row18971, row18972, row18973, row18974, row18975, row18976, row18977, row18978]

def rows6_2 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18979, row18980, row18981, row18982, row18983, row18984, row18985, row18986, row18987, row18988, row18989, row18990, row18991, row18992, row18993, row18994, row18995, row18996, row18997, row18998]

def rows6_3 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row18999, row19000, row19001, row19002, row19003, row19004, row19005, row19006, row19007, row19008, row19009, row19010, row19011, row19012, row19013, row19014, row19015, row19016, row19017, row19018]

def rows6_4 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19019, row19020, row19021, row19022, row19023, row19024, row19025, row19026, row19027, row19028, row19029, row19030, row19031, row19032, row19033, row19034, row19035, row19036, row19037, row19038]

def rows6_5 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19039, row19040, row19041, row19042, row19043, row19044, row19045, row19046, row19047, row19048, row19049, row19050, row19051, row19052, row19053, row19054, row19055, row19056, row19057, row19058]

def rows6_6 : Fin GramFunctions.Block5.form6.size → Integer.Sparse Key := ![row19059, row19060, row19061, row19062, row19063, row19064, row19065, row19066, row19067, row19068, row19069, row19070, row19071, row19072, row19073, row19074, row19075, row19076, row19077, row19078]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19079, row19080, row19081, row19082, row19083, row19084, row19085, row19086, row19087, row19088, row19089, row19090, row19091, row19092, row19093, row19094, row19095, row19096, row19097, row19098]

def rows7_1 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19099, row19100, row19101, row19102, row19103, row19104, row19105, row19106, row19107, row19108, row19109, row19110, row19111, row19112, row19113, row19114, row19115, row19116, row19117, row19118]

def rows7_2 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19119, row19120, row19121, row19122, row19123, row19124, row19125, row19126, row19127, row19128, row19129, row19130, row19131, row19132, row19133, row19134, row19135, row19136, row19137, row19138]

def rows7_3 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19139, row19140, row19141, row19142, row19143, row19144, row19145, row19146, row19147, row19148, row19149, row19150, row19151, row19152, row19153, row19154, row19155, row19156, row19157, row19158]

def rows7_4 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19159, row19160, row19161, row19162, row19163, row19164, row19165, row19166, row19167, row19168, row19169, row19170, row19171, row19172, row19173, row19174, row19175, row19176, row19177, row19178]

def rows7_5 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19179, row19180, row19181, row19182, row19183, row19184, row19185, row19186, row19187, row19188, row19189, row19190, row19191, row19192, row19193, row19194, row19195, row19196, row19197, row19198]

def rows7_6 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19199, row19200, row19201, row19202, row19203, row19204, row19205, row19206, row19207, row19208, row19209, row19210, row19211, row19212, row19213, row19214, row19215, row19216, row19217, row19218]

def rows7_7 : Fin GramFunctions.Block5.form7.size → Integer.Sparse Key := ![row19219, row19220, row19221, row19222, row19223, row19224, row19225, row19226, row19227, row19228, row19229, row19230, row19231, row19232, row19233, row19234, row19235, row19236, row19237, row19238]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19239, row19240, row19241, row19242, row19243]

def rows8_1 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19244, row19245, row19246, row19247, row19248]

def rows8_2 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19249, row19250, row19251, row19252, row19253]

def rows8_3 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19254, row19255, row19256, row19257, row19258]

def rows8_4 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19259, row19260, row19261, row19262, row19263]

def rows8_5 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19264, row19265, row19266, row19267, row19268]

def rows8_6 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19269, row19270, row19271, row19272, row19273]

def rows8_7 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19274, row19275, row19276, row19277, row19278]

def rows8_8 : Fin GramFunctions.Block5.form8.size → Integer.Sparse Key := ![row19279, row19280, row19281, row19282, row19283]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19284, row19285, row19286, row19287, row19288, row19289, row19290, row19291, row19292, row19293]

def rows9_1 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19294, row19295, row19296, row19297, row19298, row19299, row19300, row19301, row19302, row19303]

def rows9_2 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19304, row19305, row19306, row19307, row19308, row19309, row19310, row19311, row19312, row19313]

def rows9_3 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19314, row19315, row19316, row19317, row19318, row19319, row19320, row19321, row19322, row19323]

def rows9_4 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19324, row19325, row19326, row19327, row19328, row19329, row19330, row19331, row19332, row19333]

def rows9_5 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19334, row19335, row19336, row19337, row19338, row19339, row19340, row19341, row19342, row19343]

def rows9_6 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19344, row19345, row19346, row19347, row19348, row19349, row19350, row19351, row19352, row19353]

def rows9_7 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19354, row19355, row19356, row19357, row19358, row19359, row19360, row19361, row19362, row19363]

def rows9_8 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19364, row19365, row19366, row19367, row19368, row19369, row19370, row19371, row19372, row19373]

def rows9_9 : Fin GramFunctions.Block5.form9.size → Integer.Sparse Key := ![row19374, row19375, row19376, row19377, row19378, row19379, row19380, row19381, row19382, row19383]

end MUB6.Certificate.GramEntries.Block5

end OAI
end


