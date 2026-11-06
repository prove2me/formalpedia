-- Prove2me | Definitions.Def_OAIQ106E027
-- name    : OAIQ106E027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:45:50.856219+00:00
-- url     : https://prove2.me/theorems/6c638aab-fac3-4a3d-a0a7-a5d2c4cea483
-- title:
--   Definitions bundle OAIQ106E027 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 135 declarations of OpenAI's Lean: 135 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block2.rows7_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_4`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_5`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_6`, `OAI.MUB6.Certificate.GramEntries.Block2.rows7_7`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_6`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_7`, `OAI.MUB6.Certificate.GramEntries.Block2.rows8_8`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_4`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_5`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_6`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_7`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_8`, `OAI.MUB6.Certificate.GramEntries.Block2.rows9_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows10_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows11_6` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block2Row7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row7.lean), [`MutuallyUnbiased_GramEntries_Block2Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row8.lean), [`MutuallyUnbiased_GramEntries_Block2Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row9.lean), [`MutuallyUnbiased_GramEntries_Block3Row0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row0.lean), [`MutuallyUnbiased_GramEntries_Block3Row10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row10.lean), [`MutuallyUnbiased_GramEntries_Block3Row11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row11.lean), [`MutuallyUnbiased_GramEntries_Block3Row12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row12.lean), [`MutuallyUnbiased_GramEntries_Block3Row13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row13.lean), [`MutuallyUnbiased_GramEntries_Block3Row14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row14.lean), [`MutuallyUnbiased_GramEntries_Block3Row15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row15.lean), [`MutuallyUnbiased_GramEntries_Block3Row16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row16.lean), [`MutuallyUnbiased_GramEntries_Block3Row17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row17.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E025` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval7_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E025

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

def rows7_1 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6198, row6199, row6200, row6201, row6202, row6203, row6204, row6205, row6206, row6207, row6208, row6209, row6210, row6211, row6212, row6213, row6214, row6215, row6216, row6217, row6218, row6219, row6220, row6221, row6222, row6223, row6224, row6225, row6226, row6227, row6228, row6229, row6230, row6231, row6232, row6233, row6234, row6235, row6236, row6237]

def rows7_2 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6238, row6239, row6240, row6241, row6242, row6243, row6244, row6245, row6246, row6247, row6248, row6249, row6250, row6251, row6252, row6253, row6254, row6255, row6256, row6257, row6258, row6259, row6260, row6261, row6262, row6263, row6264, row6265, row6266, row6267, row6268, row6269, row6270, row6271, row6272, row6273, row6274, row6275, row6276, row6277]

def rows7_4 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6318, row6319, row6320, row6321, row6322, row6323, row6324, row6325, row6326, row6327, row6328, row6329, row6330, row6331, row6332, row6333, row6334, row6335, row6336, row6337, row6338, row6339, row6340, row6341, row6342, row6343, row6344, row6345, row6346, row6347, row6348, row6349, row6350, row6351, row6352, row6353, row6354, row6355, row6356, row6357]

def rows7_5 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6358, row6359, row6360, row6361, row6362, row6363, row6364, row6365, row6366, row6367, row6368, row6369, row6370, row6371, row6372, row6373, row6374, row6375, row6376, row6377, row6378, row6379, row6380, row6381, row6382, row6383, row6384, row6385, row6386, row6387, row6388, row6389, row6390, row6391, row6392, row6393, row6394, row6395, row6396, row6397]

def rows7_6 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6398, row6399, row6400, row6401, row6402, row6403, row6404, row6405, row6406, row6407, row6408, row6409, row6410, row6411, row6412, row6413, row6414, row6415, row6416, row6417, row6418, row6419, row6420, row6421, row6422, row6423, row6424, row6425, row6426, row6427, row6428, row6429, row6430, row6431, row6432, row6433, row6434, row6435, row6436, row6437]

def rows7_7 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6438, row6439, row6440, row6441, row6442, row6443, row6444, row6445, row6446, row6447, row6448, row6449, row6450, row6451, row6452, row6453, row6454, row6455, row6456, row6457, row6458, row6459, row6460, row6461, row6462, row6463, row6464, row6465, row6466, row6467, row6468, row6469, row6470, row6471, row6472, row6473, row6474, row6475, row6476, row6477]

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

def rows8_6 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6598, row6599, row6600, row6601, row6602, row6603, row6604, row6605, row6606, row6607, row6608, row6609, row6610, row6611, row6612, row6613, row6614, row6615, row6616, row6617, row6618, row6619, row6620, row6621, row6622, row6623, row6624, row6625, row6626, row6627, row6628, row6629, row6630, row6631, row6632, row6633, row6634, row6635, row6636, row6637]

def rows8_7 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6638, row6639, row6640, row6641, row6642, row6643, row6644, row6645, row6646, row6647, row6648, row6649, row6650, row6651, row6652, row6653, row6654, row6655, row6656, row6657, row6658, row6659, row6660, row6661, row6662, row6663, row6664, row6665, row6666, row6667, row6668, row6669, row6670, row6671, row6672, row6673, row6674, row6675, row6676, row6677]

def rows8_8 : Fin GramFunctions.Block2.form8.size → Integer.Sparse Key := ![row6678, row6679, row6680, row6681, row6682, row6683, row6684, row6685, row6686, row6687, row6688, row6689, row6690, row6691, row6692, row6693, row6694, row6695, row6696, row6697, row6698, row6699, row6700, row6701, row6702, row6703, row6704, row6705, row6706, row6707, row6708, row6709, row6710, row6711, row6712, row6713, row6714, row6715, row6716, row6717]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6718, row6719, row6720, row6721, row6722, row6723, row6724, row6725, row6726, row6727, row6728, row6729, row6730, row6731, row6732, row6733, row6734, row6735, row6736, row6737, row6738, row6739, row6740, row6741, row6742, row6743, row6744, row6745, row6746, row6747]

def rows9_1 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6748, row6749, row6750, row6751, row6752, row6753, row6754, row6755, row6756, row6757, row6758, row6759, row6760, row6761, row6762, row6763, row6764, row6765, row6766, row6767, row6768, row6769, row6770, row6771, row6772, row6773, row6774, row6775, row6776, row6777]

def rows9_2 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6778, row6779, row6780, row6781, row6782, row6783, row6784, row6785, row6786, row6787, row6788, row6789, row6790, row6791, row6792, row6793, row6794, row6795, row6796, row6797, row6798, row6799, row6800, row6801, row6802, row6803, row6804, row6805, row6806, row6807]

def rows9_3 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6808, row6809, row6810, row6811, row6812, row6813, row6814, row6815, row6816, row6817, row6818, row6819, row6820, row6821, row6822, row6823, row6824, row6825, row6826, row6827, row6828, row6829, row6830, row6831, row6832, row6833, row6834, row6835, row6836, row6837]

def rows9_4 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6838, row6839, row6840, row6841, row6842, row6843, row6844, row6845, row6846, row6847, row6848, row6849, row6850, row6851, row6852, row6853, row6854, row6855, row6856, row6857, row6858, row6859, row6860, row6861, row6862, row6863, row6864, row6865, row6866, row6867]

def rows9_5 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6868, row6869, row6870, row6871, row6872, row6873, row6874, row6875, row6876, row6877, row6878, row6879, row6880, row6881, row6882, row6883, row6884, row6885, row6886, row6887, row6888, row6889, row6890, row6891, row6892, row6893, row6894, row6895, row6896, row6897]

def rows9_6 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6898, row6899, row6900, row6901, row6902, row6903, row6904, row6905, row6906, row6907, row6908, row6909, row6910, row6911, row6912, row6913, row6914, row6915, row6916, row6917, row6918, row6919, row6920, row6921, row6922, row6923, row6924, row6925, row6926, row6927]

def rows9_7 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6928, row6929, row6930, row6931, row6932, row6933, row6934, row6935, row6936, row6937, row6938, row6939, row6940, row6941, row6942, row6943, row6944, row6945, row6946, row6947, row6948, row6949, row6950, row6951, row6952, row6953, row6954, row6955, row6956, row6957]

def rows9_8 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6958, row6959, row6960, row6961, row6962, row6963, row6964, row6965, row6966, row6967, row6968, row6969, row6970, row6971, row6972, row6973, row6974, row6975, row6976, row6977, row6978, row6979, row6980, row6981, row6982, row6983, row6984, row6985, row6986, row6987]

def rows9_9 : Fin GramFunctions.Block2.form9.size → Integer.Sparse Key := ![row6988, row6989, row6990, row6991, row6992, row6993, row6994, row6995, row6996, row6997, row6998, row6999, row7000, row7001, row7002, row7003, row7004, row7005, row7006, row7007, row7008, row7009, row7010, row7011, row7012, row7013, row7014, row7015, row7016, row7017]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block3.form0.size → Integer.Sparse Key := ![row7348, row7349, row7350, row7351, row7352, row7353, row7354, row7355, row7356, row7357, row7358, row7359, row7360, row7361, row7362, row7363, row7364, row7365, row7366, row7367, row7368, row7369, row7370, row7371]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8485, row8486, row8487, row8488, row8489, row8490, row8491, row8492, row8493, row8494, row8495, row8496, row8497, row8498, row8499, row8500]

def rows10_1 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8501, row8502, row8503, row8504, row8505, row8506, row8507, row8508, row8509, row8510, row8511, row8512, row8513, row8514, row8515, row8516]

def rows10_2 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8517, row8518, row8519, row8520, row8521, row8522, row8523, row8524, row8525, row8526, row8527, row8528, row8529, row8530, row8531, row8532]

def rows10_3 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8533, row8534, row8535, row8536, row8537, row8538, row8539, row8540, row8541, row8542, row8543, row8544, row8545, row8546, row8547, row8548]

def rows10_4 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8549, row8550, row8551, row8552, row8553, row8554, row8555, row8556, row8557, row8558, row8559, row8560, row8561, row8562, row8563, row8564]

def rows10_5 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8565, row8566, row8567, row8568, row8569, row8570, row8571, row8572, row8573, row8574, row8575, row8576, row8577, row8578, row8579, row8580]

def rows10_6 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8581, row8582, row8583, row8584, row8585, row8586, row8587, row8588, row8589, row8590, row8591, row8592, row8593, row8594, row8595, row8596]

def rows10_7 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8597, row8598, row8599, row8600, row8601, row8602, row8603, row8604, row8605, row8606, row8607, row8608, row8609, row8610, row8611, row8612]

def rows10_8 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8613, row8614, row8615, row8616, row8617, row8618, row8619, row8620, row8621, row8622, row8623, row8624, row8625, row8626, row8627, row8628]

def rows10_9 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8629, row8630, row8631, row8632, row8633, row8634, row8635, row8636, row8637, row8638, row8639, row8640, row8641, row8642, row8643, row8644]

def rows10_10 : Fin GramFunctions.Block3.form10.size → Integer.Sparse Key := ![row8645, row8646, row8647, row8648, row8649, row8650, row8651, row8652, row8653, row8654, row8655, row8656, row8657, row8658, row8659, row8660]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8661, row8662, row8663, row8664, row8665, row8666, row8667, row8668]

def rows11_1 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8669, row8670, row8671, row8672, row8673, row8674, row8675, row8676]

def rows11_2 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8677, row8678, row8679, row8680, row8681, row8682, row8683, row8684]

def rows11_3 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8685, row8686, row8687, row8688, row8689, row8690, row8691, row8692]

def rows11_4 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8693, row8694, row8695, row8696, row8697, row8698, row8699, row8700]

def rows11_5 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8701, row8702, row8703, row8704, row8705, row8706, row8707, row8708]

def rows11_6 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8709, row8710, row8711, row8712, row8713, row8714, row8715, row8716]

def rows11_7 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8717, row8718, row8719, row8720, row8721, row8722, row8723, row8724]

def rows11_8 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8725, row8726, row8727, row8728, row8729, row8730, row8731, row8732]

def rows11_9 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8733, row8734, row8735, row8736, row8737, row8738, row8739, row8740]

def rows11_10 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8741, row8742, row8743, row8744, row8745, row8746, row8747, row8748]

def rows11_11 : Fin GramFunctions.Block3.form11.size → Integer.Sparse Key := ![row8749, row8750, row8751, row8752, row8753, row8754, row8755, row8756]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row8757, row8758, row8759, row8760]

def rows12_1 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row8761, row8762, row8763, row8764]

def rows12_2 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row8765, row8766, row8767, row8768]

def rows12_3 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row8769, row8770, row8771, row8772]

def rows12_4 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row8773, row8774, row8775, row8776]

def rows12_5 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8777, row8778, row8779, row8780, row8781, row8782, row8783, row8784]

def rows12_6 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8785, row8786, row8787, row8788, row8789, row8790, row8791, row8792]

def rows12_7 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8793, row8794, row8795, row8796, row8797, row8798, row8799, row8800]

def rows12_8 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8801, row8802, row8803, row8804, row8805, row8806, row8807, row8808]

def rows12_9 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8809, row8810, row8811, row8812, row8813, row8814, row8815, row8816]

def rows12_10 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8817, row8818, row8819, row8820, row8821, row8822, row8823, row8824]

def rows12_11 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8825, row8826, row8827, row8828, row8829, row8830, row8831, row8832]

def rows12_12 : Fin GramFunctions.Block3.form12.size → Integer.Sparse Key := ![row8833, row8834, row8835, row8836, row8837, row8838, row8839, row8840]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8841, row8842, row8843, row8844, row8845, row8846, row8847, row8848, row8849, row8850, row8851, row8852, row8853, row8854, row8855, row8856]

def rows13_1 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8857, row8858, row8859, row8860, row8861, row8862, row8863, row8864, row8865, row8866, row8867, row8868, row8869, row8870, row8871, row8872]

def rows13_2 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8873, row8874, row8875, row8876, row8877, row8878, row8879, row8880, row8881, row8882, row8883, row8884, row8885, row8886, row8887, row8888]

def rows13_3 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8889, row8890, row8891, row8892, row8893, row8894, row8895, row8896, row8897, row8898, row8899, row8900, row8901, row8902, row8903, row8904]

def rows13_4 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8905, row8906, row8907, row8908, row8909, row8910, row8911, row8912, row8913, row8914, row8915, row8916, row8917, row8918, row8919, row8920]

def rows13_5 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8921, row8922, row8923, row8924, row8925, row8926, row8927, row8928, row8929, row8930, row8931, row8932, row8933, row8934, row8935, row8936]

def rows13_6 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8937, row8938, row8939, row8940, row8941, row8942, row8943, row8944, row8945, row8946, row8947, row8948, row8949, row8950, row8951, row8952]

def rows13_7 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8953, row8954, row8955, row8956, row8957, row8958, row8959, row8960, row8961, row8962, row8963, row8964, row8965, row8966, row8967, row8968]

def rows13_8 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8969, row8970, row8971, row8972, row8973, row8974, row8975, row8976, row8977, row8978, row8979, row8980, row8981, row8982, row8983, row8984]

def rows13_9 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row8985, row8986, row8987, row8988, row8989, row8990, row8991, row8992, row8993, row8994, row8995, row8996, row8997, row8998, row8999, row9000]

def rows13_10 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9001, row9002, row9003, row9004, row9005, row9006, row9007, row9008, row9009, row9010, row9011, row9012, row9013, row9014, row9015, row9016]

def rows13_11 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9017, row9018, row9019, row9020, row9021, row9022, row9023, row9024, row9025, row9026, row9027, row9028, row9029, row9030, row9031, row9032]

def rows13_12 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9033, row9034, row9035, row9036, row9037, row9038, row9039, row9040, row9041, row9042, row9043, row9044, row9045, row9046, row9047, row9048]

def rows13_13 : Fin GramFunctions.Block3.form13.size → Integer.Sparse Key := ![row9049, row9050, row9051, row9052, row9053, row9054, row9055, row9056, row9057, row9058, row9059, row9060, row9061, row9062, row9063, row9064]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row9065, row9066, row9067, row9068]

def rows14_1 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row9069, row9070, row9071, row9072]

def rows14_2 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row9073, row9074, row9075, row9076]

def rows14_3 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9077, row9078, row9079, row9080, row9081, row9082, row9083, row9084]

def rows14_4 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9085, row9086, row9087, row9088, row9089, row9090, row9091, row9092]

def rows14_5 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9093, row9094, row9095, row9096, row9097, row9098, row9099, row9100]

def rows14_6 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9101, row9102, row9103, row9104, row9105, row9106, row9107, row9108]

def rows14_7 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9109, row9110, row9111, row9112, row9113, row9114, row9115, row9116]

def rows14_8 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9117, row9118, row9119, row9120, row9121, row9122, row9123, row9124]

def rows14_9 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9125, row9126, row9127, row9128, row9129, row9130, row9131, row9132]

def rows14_10 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9133, row9134, row9135, row9136, row9137, row9138, row9139, row9140]

def rows14_11 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9141, row9142, row9143, row9144, row9145, row9146, row9147, row9148]

def rows14_12 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9149, row9150, row9151, row9152, row9153, row9154, row9155, row9156]

def rows14_13 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9157, row9158, row9159, row9160, row9161, row9162, row9163, row9164]

def rows14_14 : Fin GramFunctions.Block3.form14.size → Integer.Sparse Key := ![row9165, row9166, row9167, row9168, row9169, row9170, row9171, row9172]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8661, row8662, row8663, row8664, row9173, row9174, row9175, row9176, row9177, row9178, row9179, row9180, row9181, row9182, row9183, row9184]

def rows15_1 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8669, row8670, row8671, row8672, row9185, row9186, row9187, row9188, row9189, row9190, row9191, row9192, row9193, row9194, row9195, row9196]

def rows15_2 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8677, row8678, row8679, row8680, row9197, row9198, row9199, row9200, row9201, row9202, row9203, row9204, row9205, row9206, row9207, row9208]

def rows15_3 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8685, row8686, row8687, row8688, row9209, row9210, row9211, row9212, row9213, row9214, row9215, row9216, row9217, row9218, row9219, row9220]

def rows15_4 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8693, row8694, row8695, row8696, row9221, row9222, row9223, row9224, row9225, row9226, row9227, row9228, row9229, row9230, row9231, row9232]

def rows15_5 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8701, row8702, row8703, row8704, row9233, row9234, row9235, row9236, row9237, row9238, row9239, row9240, row9241, row9242, row9243, row9244]

def rows15_6 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8709, row8710, row8711, row8712, row9245, row9246, row9247, row9248, row9249, row9250, row9251, row9252, row9253, row9254, row9255, row9256]

def rows15_7 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8717, row8718, row8719, row8720, row9257, row9258, row9259, row9260, row9261, row9262, row9263, row9264, row9265, row9266, row9267, row9268]

def rows15_8 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8725, row8726, row8727, row8728, row9269, row9270, row9271, row9272, row9273, row9274, row9275, row9276, row9277, row9278, row9279, row9280]

def rows15_9 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8733, row8734, row8735, row8736, row9281, row9282, row9283, row9284, row9285, row9286, row9287, row9288, row9289, row9290, row9291, row9292]

def rows15_10 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8741, row8742, row8743, row8744, row9293, row9294, row9295, row9296, row9297, row9298, row9299, row9300, row9301, row9302, row9303, row9304]

def rows15_11 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8749, row8750, row8751, row8752, row9305, row9306, row9307, row9308, row9309, row9310, row9311, row9312, row9313, row9314, row9315, row9316]

def rows15_12 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9317, row9318, row9319, row9320, row9321, row9322, row9323, row9324, row9325, row9326, row9327, row9328, row9329, row9330, row9331, row9332]

def rows15_13 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9333, row9334, row9335, row9336, row9337, row9338, row9339, row9340, row9341, row9342, row9343, row9344, row9345, row9346, row9347, row9348]

def rows15_14 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9349, row9350, row9351, row9352, row9353, row9354, row9355, row9356, row9357, row9358, row9359, row9360, row9361, row9362, row9363, row9364]

def rows15_15 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9365, row9366, row9367, row9368, row9369, row9370, row9371, row9372, row9373, row9374, row9375, row9376, row9377, row9378, row9379, row9380]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9381, row9382, row9383, row9384, row7430, row7431, row7432, row7433]

def rows16_1 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9385, row9386, row9387, row9388, row7446, row7447, row7448, row7449]

def rows16_2 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9389, row9390, row9391, row9392, row7462, row7463, row7464, row7465]

def rows16_3 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9393, row9394, row9395, row9396, row7478, row7479, row7480, row7481]

def rows16_4 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9397, row9398, row9399, row9400, row9401, row9402, row9403, row9404]

def rows16_5 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9405, row9406, row9407, row9408, row9409, row9410, row9411, row9412]

def rows16_6 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9413, row9414, row9415, row9416, row9417, row9418, row9419, row9420]

def rows16_7 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9421, row9422, row9423, row9424, row9425, row9426, row9427, row9428]

def rows16_8 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9429, row9430, row9431, row9432, row9433, row9434, row9435, row9436]

def rows16_9 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9437, row9438, row9439, row9440, row9441, row9442, row9443, row9444]

def rows16_10 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9445, row9446, row9447, row9448, row9449, row9450, row9451, row9452]

def rows16_11 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9453, row9454, row9455, row9456, row9457, row9458, row9459, row9460]

def rows16_12 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9461, row9462, row9463, row9464, row9465, row9466, row9467, row9468]

def rows16_13 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9469, row9470, row9471, row9472, row9473, row9474, row9475, row9476]

def rows16_14 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9477, row9478, row9479, row9480, row9481, row9482, row9483, row9484]

def rows16_15 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9485, row9486, row9487, row9488, row9489, row9490, row9491, row9492]

def rows16_16 : Fin GramFunctions.Block3.form16.size → Integer.Sparse Key := ![row9493, row9494, row9495, row9496, row9497, row9498, row9499, row9500]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9501, row9502, row9503, row9504, row9505, row9506, row9507, row9508, row9509, row9510, row9511, row9512, row9513, row9514, row9515, row9516, row9517, row9518, row9519, row9520, row9521, row9522, row9523, row9524]

def rows17_1 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9525, row9526, row9527, row9528, row9529, row9530, row9531, row9532, row9533, row9534, row9535, row9536, row9537, row9538, row9539, row9540, row9541, row9542, row9543, row9544, row9545, row9546, row9547, row9548]

def rows17_2 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9549, row9550, row9551, row9552, row9553, row9554, row9555, row9556, row9557, row9558, row9559, row9560, row9561, row9562, row9563, row9564, row9565, row9566, row9567, row9568, row9569, row9570, row9571, row9572]

def rows17_3 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9573, row9574, row9575, row9576, row9577, row9578, row9579, row9580, row9581, row9582, row9583, row9584, row9585, row9586, row9587, row9588, row9589, row9590, row9591, row9592, row9593, row9594, row9595, row9596]

def rows17_4 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9597, row9598, row9599, row9600, row9601, row9602, row9603, row9604, row9605, row9606, row9607, row9608, row9609, row9610, row9611, row9612, row9613, row9614, row9615, row9616, row9617, row9618, row9619, row9620]

def rows17_5 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9621, row9622, row9623, row9624, row9625, row9626, row9627, row9628, row9629, row9630, row9631, row9632, row9633, row9634, row9635, row9636, row9637, row9638, row9639, row9640, row9641, row9642, row9643, row9644]

def rows17_6 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9645, row9646, row9647, row9648, row9649, row9650, row9651, row9652, row9653, row9654, row9655, row9656, row9657, row9658, row9659, row9660, row9661, row9662, row9663, row9664, row9665, row9666, row9667, row9668]

def rows17_7 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9669, row9670, row9671, row9672, row9673, row9674, row9675, row9676, row9677, row9678, row9679, row9680, row9681, row9682, row9683, row9684, row9685, row9686, row9687, row9688, row9689, row9690, row9691, row9692]

def rows17_8 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9693, row9694, row9695, row9696, row9697, row9698, row9699, row9700, row9701, row9702, row9703, row9704, row9705, row9706, row9707, row9708, row9709, row9710, row9711, row9712, row9713, row9714, row9715, row9716]

def rows17_10 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9741, row9742, row9743, row9744, row9745, row9746, row9747, row9748, row9749, row9750, row9751, row9752, row9753, row9754, row9755, row9756, row9757, row9758, row9759, row9760, row9761, row9762, row9763, row9764]

def rows17_11 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9765, row9766, row9767, row9768, row9769, row9770, row9771, row9772, row9773, row9774, row9775, row9776, row9777, row9778, row9779, row9780, row9781, row9782, row9783, row9784, row9785, row9786, row9787, row9788]

def rows17_12 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9789, row9790, row9791, row9792, row9793, row9794, row9795, row9796, row9797, row9798, row9799, row9800, row9801, row9802, row9803, row9804, row9805, row9806, row9807, row9808, row9809, row9810, row9811, row9812]

def rows17_13 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9813, row9814, row9815, row9816, row9817, row9818, row9819, row9820, row9821, row9822, row9823, row9824, row9825, row9826, row9827, row9828, row9829, row9830, row9831, row9832, row9833, row9834, row9835, row9836]

def rows17_14 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9837, row9838, row9839, row9840, row9841, row9842, row9843, row9844, row9845, row9846, row9847, row9848, row9849, row9850, row9851, row9852, row9853, row9854, row9855, row9856, row9857, row9858, row9859, row9860]

def rows17_15 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9861, row9862, row9863, row9864, row9865, row9866, row9867, row9868, row9869, row9870, row9871, row9872, row9873, row9874, row9875, row9876, row9877, row9878, row9879, row9880, row9881, row9882, row9883, row9884]

def rows17_16 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9885, row9886, row9887, row9888, row9889, row9890, row9891, row9892, row9893, row9894, row9895, row9896, row9897, row9898, row9899, row9900, row9901, row9902, row9903, row9904, row9905, row9906, row9907, row9908]

def rows17_17 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9909, row9910, row9911, row9912, row9913, row9914, row9915, row9916, row9917, row9918, row9919, row9920, row9921, row9922, row9923, row9924, row9925, row9926, row9927, row9928, row9929, row9930, row9931, row9932]

end MUB6.Certificate.GramEntries.Block3

end OAI
end


