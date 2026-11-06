-- Prove2me | Definitions.Def_OAIQ106E037
-- name    : OAIQ106E037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:58:46.161895+00:00
-- url     : https://prove2.me/theorems/05953f66-ee12-4d83-8ff9-a0b0fa6e79be
-- title:
--   Definitions bundle OAIQ106E037 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 179 declarations of OpenAI's Lean: 179 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block4.rows16_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_11`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_12`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_13`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_14`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_15`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_16`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_4`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_5`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_6`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_7`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_8`, `OAI.MUB6.Certificate.GramEntries.Block4.rows16_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_11`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_12`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_13`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_14`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_15`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_16`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_17`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_4`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_5`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_6`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_7`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_8`, `OAI.MUB6.Certificate.GramEntries.Block4.rows17_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows18_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows18_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows18_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows18_11`, `OAI.MUB6.Certificate.GramEntries.Block4.rows18_12` and 139 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block4Row1`, `MutuallyUnbiased_GramEntries_Block4Row16`, `MutuallyUnbiased_GramEntries_Block4Row17`, `MutuallyUnbiased_GramEntries_Block4Row18`, `MutuallyUnbiased_GramEntries_Block4Row19`, `MutuallyUnbiased_GramEntries_Block4Row2`, `MutuallyUnbiased_GramEntries_Block4Row20`, `MutuallyUnbiased_GramEntries_Block4Row21`, `MutuallyUnbiased_GramEntries_Block4Row3`, `MutuallyUnbiased_GramEntries_Block4Row4`, `MutuallyUnbiased_GramEntries_Block4Row5`, `MutuallyUnbiased_GramEntries_Block4Row7`, `MutuallyUnbiased_GramEntries_Block4Row8`, `MutuallyUnbiased_GramEntries_Block4Row9`, `MutuallyUnbiased_GramEntries_Block5Row0`, `MutuallyUnbiased_GramEntries_Block5Row10`, `MutuallyUnbiased_GramEntries_Block5Row11`.
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E035` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval8_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E035

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13205, row13206, row13207, row13208, row13209, row13210, row13211, row13212, row13213, row13214, row13215, row13216, row13217, row13218, row13219, row13220, row13221, row13222, row13223, row13224]

def rows1_1 : Fin GramFunctions.Block4.form1.size → Integer.Sparse Key := ![row13225, row13226, row13227, row13228, row13229, row13230, row13231, row13232, row13233, row13234, row13235, row13236, row13237, row13238, row13239, row13240, row13241, row13242, row13243, row13244]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16095, row16096, row16097, row16098, row16099, row16100, row16101, row16102, row16103, row16104, row16105, row16106, row16107, row16108, row16109, row16110, row16111, row16112, row16113, row16114, row16115, row16116, row16117, row16118, row16119, row16120, row16121, row16122, row16123, row16124, row16125, row16126, row16127, row16128, row16129, row16130]

def rows16_1 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16131, row16132, row16133, row16134, row16135, row16136, row16137, row16138, row16139, row16140, row16141, row16142, row16143, row16144, row16145, row16146, row16147, row16148, row16149, row16150, row16151, row16152, row16153, row16154, row16155, row16156, row16157, row16158, row16159, row16160, row16161, row16162, row16163, row16164, row16165, row16166]

def rows16_2 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16167, row16168, row16169, row16170, row16171, row16172, row16173, row16174, row16175, row16176, row16177, row16178, row16179, row16180, row16181, row16182, row16183, row16184, row16185, row16186, row16187, row16188, row16189, row16190, row16191, row16192, row16193, row16194, row16195, row16196, row16197, row16198, row16199, row16200, row16201, row16202]

def rows16_3 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16203, row16204, row16205, row16206, row16207, row16208, row16209, row16210, row16211, row16212, row16213, row16214, row16215, row16216, row16217, row16218, row16219, row16220, row16221, row16222, row16223, row16224, row16225, row16226, row16227, row16228, row16229, row16230, row16231, row16232, row16233, row16234, row16235, row16236, row16237, row16238]

def rows16_4 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16239, row16240, row16241, row16242, row16243, row16244, row16245, row16246, row16247, row16248, row16249, row16250, row16251, row16252, row16253, row16254, row16255, row16256, row16257, row16258, row16259, row16260, row16261, row16262, row16263, row16264, row16265, row16266, row16267, row16268, row16269, row16270, row16271, row16272, row16273, row16274]

def rows16_5 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16275, row16276, row16277, row16278, row16279, row16280, row16281, row16282, row16283, row16284, row16285, row16286, row16287, row16288, row16289, row16290, row16291, row16292, row16293, row16294, row16295, row16296, row16297, row16298, row16299, row16300, row16301, row16302, row16303, row16304, row16305, row16306, row16307, row16308, row16309, row16310]

def rows16_6 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16311, row16312, row16313, row16314, row16315, row16316, row16317, row16318, row16319, row16320, row16321, row16322, row16323, row16324, row16325, row16326, row16327, row16328, row16329, row16330, row16331, row16332, row16333, row16334, row16335, row16336, row16337, row16338, row16339, row16340, row16341, row16342, row16343, row16344, row16345, row16346]

def rows16_7 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16347, row16348, row16349, row16350, row16351, row16352, row16353, row16354, row16355, row16356, row16357, row16358, row16359, row16360, row16361, row16362, row16363, row16364, row16365, row16366, row16367, row16368, row16369, row16370, row16371, row16372, row16373, row16374, row16375, row16376, row16377, row16378, row16379, row16380, row16381, row16382]

def rows16_8 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16383, row16384, row16385, row16386, row16387, row16388, row16389, row16390, row16391, row16392, row16393, row16394, row16395, row16396, row16397, row16398, row16399, row16400, row16401, row16402, row16403, row16404, row16405, row16406, row16407, row16408, row16409, row16410, row16411, row16412, row16413, row16414, row16415, row16416, row16417, row16418]

def rows16_9 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16419, row16420, row16421, row16422, row16423, row16424, row16425, row16426, row16427, row16428, row16429, row16430, row16431, row16432, row16433, row16434, row16435, row16436, row16437, row16438, row16439, row16440, row16441, row16442, row16443, row16444, row16445, row16446, row16447, row16448, row16449, row16450, row16451, row16452, row16453, row16454]

def rows16_10 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16455, row16456, row16457, row16458, row16459, row16460, row16461, row16462, row16463, row16464, row16465, row16466, row16467, row16468, row16469, row16470, row16471, row16472, row16473, row16474, row16475, row16476, row16477, row16478, row16479, row16480, row16481, row16482, row16483, row16484, row16485, row16486, row16487, row16488, row16489, row16490]

def rows16_11 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16491, row16492, row16493, row16494, row16495, row16496, row16497, row16498, row16499, row16500, row16501, row16502, row16503, row16504, row16505, row16506, row16507, row16508, row16509, row16510, row16511, row16512, row16513, row16514, row16515, row16516, row16517, row16518, row16519, row16520, row16521, row16522, row16523, row16524, row16525, row16526]

def rows16_12 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16527, row16528, row16529, row16530, row16531, row16532, row16533, row16534, row16535, row16536, row16537, row16538, row16539, row16540, row16541, row16542, row16543, row16544, row16545, row16546, row16547, row16548, row16549, row16550, row16551, row16552, row16553, row16554, row16555, row16556, row16557, row16558, row16559, row16560, row16561, row16562]

def rows16_13 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16563, row16564, row16565, row16566, row16567, row16568, row16569, row16570, row16571, row16572, row16573, row16574, row16575, row16576, row16577, row16578, row16579, row16580, row16581, row16582, row16583, row16584, row16585, row16586, row16587, row16588, row16589, row16590, row16591, row16592, row16593, row16594, row16595, row16596, row16597, row16598]

def rows16_14 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16599, row16600, row16601, row16602, row16603, row16604, row16605, row16606, row16607, row16608, row16609, row16610, row16611, row16612, row16613, row16614, row16615, row16616, row16617, row16618, row16619, row16620, row16621, row16622, row16623, row16624, row16625, row16626, row16627, row16628, row16629, row16630, row16631, row16632, row16633, row16634]

def rows16_15 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16635, row16636, row16637, row16638, row16639, row16640, row16641, row16642, row16643, row16644, row16645, row16646, row16647, row16648, row16649, row16650, row16651, row16652, row16653, row16654, row16655, row16656, row16657, row16658, row16659, row16660, row16661, row16662, row16663, row16664, row16665, row16666, row16667, row16668, row16669, row16670]

def rows16_16 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16671, row16672, row16673, row16674, row16675, row16676, row16677, row16678, row16679, row16680, row16681, row16682, row16683, row16684, row16685, row16686, row16687, row16688, row16689, row16690, row16691, row16692, row16693, row16694, row16695, row16696, row16697, row16698, row16699, row16700, row16701, row16702, row16703, row16704, row16705, row16706]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16707, row16708, row16709, row16710, row16711, row16712, row16713, row16714, row16715, row16716, row16717, row16718, row16719, row16720, row16721, row16722, row16723, row16724]

def rows17_1 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16725, row16726, row16727, row16728, row16729, row16730, row16731, row16732, row16733, row16734, row16735, row16736, row16737, row16738, row16739, row16740, row16741, row16742]

def rows17_2 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16743, row16744, row16745, row16746, row16747, row16748, row16749, row16750, row16751, row16752, row16753, row16754, row16755, row16756, row16757, row16758, row16759, row16760]

def rows17_3 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16761, row16762, row16763, row16764, row16765, row16766, row16767, row16768, row16769, row16770, row16771, row16772, row16773, row16774, row16775, row16776, row16777, row16778]

def rows17_4 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16779, row16780, row16781, row16782, row16783, row16784, row16785, row16786, row16787, row16788, row16789, row16790, row16791, row16792, row16793, row16794, row16795, row16796]

def rows17_5 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16797, row16798, row16799, row16800, row16801, row16802, row16803, row16804, row16805, row16806, row16807, row16808, row16809, row16810, row16811, row16812, row16813, row16814]

def rows17_6 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16815, row16816, row16817, row16818, row16819, row16820, row16821, row16822, row16823, row16824, row16825, row16826, row16827, row16828, row16829, row16830, row16831, row16832]

def rows17_7 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16833, row16834, row16835, row16836, row16837, row16838, row16839, row16840, row16841, row16842, row16843, row16844, row16845, row16846, row16847, row16848, row16849, row16850]

def rows17_8 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16851, row16852, row16853, row16854, row16855, row16856, row16857, row16858, row16859, row16860, row16861, row16862, row16863, row16864, row16865, row16866, row16867, row16868]

def rows17_9 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16869, row16870, row16871, row16872, row16873, row16874, row16875, row16876, row16877, row16878, row16879, row16880, row16881, row16882, row16883, row16884, row16885, row16886]

def rows17_10 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16887, row16888, row16889, row16890, row16891, row16892, row16893, row16894, row16895, row16896, row16897, row16898, row16899, row16900, row16901, row16902, row16903, row16904]

def rows17_11 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16905, row16906, row16907, row16908, row16909, row16910, row16911, row16912, row16913, row16914, row16915, row16916, row16917, row16918, row16919, row16920, row16921, row16922]

def rows17_12 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16923, row16924, row16925, row16926, row16927, row16928, row16929, row16930, row16931, row16932, row16933, row16934, row16935, row16936, row16937, row16938, row16939, row16940]

def rows17_13 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16941, row16942, row16943, row16944, row16945, row16946, row16947, row16948, row16949, row16950, row16951, row16952, row16953, row16954, row16955, row16956, row16957, row16958]

def rows17_14 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16959, row16960, row16961, row16962, row16963, row16964, row16965, row16966, row16967, row16968, row16969, row16970, row16971, row16972, row16973, row16974, row16975, row16976]

def rows17_15 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16977, row16978, row16979, row16980, row16981, row16982, row16983, row16984, row16985, row16986, row16987, row16988, row16989, row16990, row16991, row16992, row16993, row16994]

def rows17_16 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row16995, row16996, row16997, row16998, row16999, row17000, row17001, row17002, row17003, row17004, row17005, row17006, row17007, row17008, row17009, row17010, row17011, row17012]

def rows17_17 : Fin GramFunctions.Block4.form17.size → Integer.Sparse Key := ![row17013, row17014, row17015, row17016, row17017, row17018, row17019, row17020, row17021, row17022, row17023, row17024, row17025, row17026, row17027, row17028, row17029, row17030]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17031, row17032, row17033, row17034, row17035, row17036, row17037, row17038, row17039, row17040, row17041, row17042, row17043, row17044, row17045, row17046, row17047, row17048, row17049, row17050]

def rows18_1 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17051, row17052, row17053, row17054, row17055, row17056, row17057, row17058, row17059, row17060, row17061, row17062, row17063, row17064, row17065, row17066, row17067, row17068, row17069, row17070]

def rows18_2 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17071, row17072, row17073, row17074, row17075, row17076, row17077, row17078, row17079, row17080, row17081, row17082, row17083, row17084, row17085, row17086, row17087, row17088, row17089, row17090]

def rows18_3 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17091, row17092, row17093, row17094, row17095, row17096, row17097, row17098, row17099, row17100, row17101, row17102, row17103, row17104, row17105, row17106, row17107, row17108, row17109, row17110]

def rows18_4 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17111, row17112, row17113, row17114, row17115, row17116, row17117, row17118, row17119, row17120, row17121, row17122, row17123, row17124, row17125, row17126, row17127, row17128, row17129, row17130]

def rows18_5 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17131, row17132, row17133, row17134, row17135, row17136, row17137, row17138, row17139, row17140, row17141, row17142, row17143, row17144, row17145, row17146, row17147, row17148, row17149, row17150]

def rows18_6 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17151, row17152, row17153, row17154, row17155, row17156, row17157, row17158, row17159, row17160, row17161, row17162, row17163, row17164, row17165, row17166, row17167, row17168, row17169, row17170]

def rows18_7 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17171, row17172, row17173, row17174, row17175, row17176, row17177, row17178, row17179, row17180, row17181, row17182, row17183, row17184, row17185, row17186, row17187, row17188, row17189, row17190]

def rows18_8 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17191, row17192, row17193, row17194, row17195, row17196, row17197, row17198, row17199, row17200, row17201, row17202, row17203, row17204, row17205, row17206, row17207, row17208, row17209, row17210]

def rows18_9 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17211, row17212, row17213, row17214, row17215, row17216, row17217, row17218, row17219, row17220, row17221, row17222, row17223, row17224, row17225, row17226, row17227, row17228, row17229, row17230]

def rows18_10 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17231, row17232, row17233, row17234, row17235, row17236, row17237, row17238, row17239, row17240, row17241, row17242, row17243, row17244, row17245, row17246, row17247, row17248, row17249, row17250]

def rows18_11 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17251, row17252, row17253, row17254, row17255, row17256, row17257, row17258, row17259, row17260, row17261, row17262, row17263, row17264, row17265, row17266, row17267, row17268, row17269, row17270]

def rows18_12 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17271, row17272, row17273, row17274, row17275, row17276, row17277, row17278, row17279, row17280, row17281, row17282, row17283, row17284, row17285, row17286, row17287, row17288, row17289, row17290]

def rows18_13 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17291, row17292, row17293, row17294, row17295, row17296, row17297, row17298, row17299, row17300, row17301, row17302, row17303, row17304, row17305, row17306, row17307, row17308, row17309, row17310]

def rows18_14 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17311, row17312, row17313, row17314, row17315, row17316, row17317, row17318, row17319, row17320, row17321, row17322, row17323, row17324, row17325, row17326, row17327, row17328, row17329, row17330]

def rows18_15 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17331, row17332, row17333, row17334, row17335, row17336, row17337, row17338, row17339, row17340, row17341, row17342, row17343, row17344, row17345, row17346, row17347, row17348, row17349, row17350]

def rows18_16 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17351, row17352, row17353, row17354, row17355, row17356, row17357, row17358, row17359, row17360, row17361, row17362, row17363, row17364, row17365, row17366, row17367, row17368, row17369, row17370]

def rows18_17 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17371, row17372, row17373, row17374, row17375, row17376, row17377, row17378, row17379, row17380, row17381, row17382, row17383, row17384, row17385, row17386, row17387, row17388, row17389, row17390]

def rows18_18 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17391, row17392, row17393, row17394, row17395, row17396, row17397, row17398, row17399, row17400, row17401, row17402, row17403, row17404, row17405, row17406, row17407, row17408, row17409, row17410]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17411, row17412, row17413, row17414, row17415, row17416, row17417, row17418, row17419, row17420]

def rows19_1 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17421, row17422, row17423, row17424, row17425, row17426, row17427, row17428, row17429, row17430]

def rows19_2 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17431, row17432, row17433, row17434, row17435, row17436, row17437, row17438, row17439, row17440]

def rows19_3 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17441, row17442, row17443, row17444, row17445, row17446, row17447, row17448, row17449, row17450]

def rows19_4 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17451, row17452, row17453, row17454, row17455, row17456, row17457, row17458, row17459, row17460]

def rows19_5 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17461, row17462, row17463, row17464, row17465, row17466, row17467, row17468, row17469, row17470]

def rows19_6 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17471, row17472, row17473, row17474, row17475, row17476, row17477, row17478, row17479, row17480]

def rows19_7 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17481, row17482, row17483, row17484, row17485, row17486, row17487, row17488, row17489, row17490]

def rows19_8 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17491, row17492, row17493, row17494, row17495, row17496, row17497, row17498, row17499, row17500]

def rows19_9 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17501, row17502, row17503, row17504, row17505, row17506, row17507, row17508, row17509, row17510]

def rows19_10 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17511, row17512, row17513, row17514, row17515, row17516, row17517, row17518, row17519, row17520]

def rows19_11 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17521, row17522, row17523, row17524, row17525, row17526, row17527, row17528, row17529, row17530]

def rows19_12 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17531, row17532, row17533, row17534, row17535, row17536, row17537, row17538, row17539, row17540]

def rows19_13 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17541, row17542, row17543, row17544, row17545, row17546, row17547, row17548, row17549, row17550]

def rows19_14 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17551, row17552, row17553, row17554, row17555, row17556, row17557, row17558, row17559, row17560]

def rows19_15 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17561, row17562, row17563, row17564, row17565, row17566, row17567, row17568, row17569, row17570]

def rows19_16 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17571, row17572, row17573, row17574, row17575, row17576, row17577, row17578, row17579, row17580]

def rows19_17 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17581, row17582, row17583, row17584, row17585, row17586, row17587, row17588, row17589, row17590]

def rows19_18 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17591, row17592, row17593, row17594, row17595, row17596, row17597, row17598, row17599, row17600]

def rows19_19 : Fin GramFunctions.Block4.form19.size → Integer.Sparse Key := ![row17601, row17602, row17603, row17604, row17605, row17606, row17607, row17608, row17609, row17610]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13245, row13246, row13247, row13248, row13249, row13250, row13251, row13252, row13253, row13254, row13255, row13256, row13257, row13258, row13259, row13260, row13261, row13262, row13263, row13264]

def rows2_1 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13265, row13266, row13267, row13268, row13269, row13270, row13271, row13272, row13273, row13274, row13275, row13276, row13277, row13278, row13279, row13280, row13281, row13282, row13283, row13284]

def rows2_2 : Fin GramFunctions.Block4.form2.size → Integer.Sparse Key := ![row13285, row13286, row13287, row13288, row13289, row13290, row13291, row13292, row13293, row13294, row13295, row13296, row13297, row13298, row13299, row13300, row13301, row13302, row13303, row13304]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17611, row17612, row17613, row17614, row17615, row17616, row17617, row17618, row17619, row17620, row17621, row17622, row17623, row17624, row17625, row17626, row17627, row17628]

def rows20_1 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17629, row17630, row17631, row17632, row17633, row17634, row17635, row17636, row17637, row17638, row17639, row17640, row17641, row17642, row17643, row17644, row17645, row17646]

def rows20_2 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17647, row17648, row17649, row17650, row17651, row17652, row17653, row17654, row17655, row17656, row17657, row17658, row17659, row17660, row17661, row17662, row17663, row17664]

def rows20_3 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17665, row17666, row17667, row17668, row17669, row17670, row17671, row17672, row17673, row17674, row17675, row17676, row17677, row17678, row17679, row17680, row17681, row17682]

def rows20_4 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17683, row17684, row17685, row17686, row17687, row17688, row17689, row17690, row17691, row17692, row17693, row17694, row17695, row17696, row17697, row17698, row17699, row17700]

def rows20_5 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17701, row17702, row17703, row17704, row17705, row17706, row17707, row17708, row17709, row17710, row17711, row17712, row17713, row17714, row17715, row17716, row17717, row17718]

def rows20_6 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17719, row17720, row17721, row17722, row17723, row17724, row17725, row17726, row17727, row17728, row17729, row17730, row17731, row17732, row17733, row17734, row17735, row17736]

def rows20_7 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17737, row17738, row17739, row17740, row17741, row17742, row17743, row17744, row17745, row17746, row17747, row17748, row17749, row17750, row17751, row17752, row17753, row17754]

def rows20_8 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17755, row17756, row17757, row17758, row17759, row17760, row17761, row17762, row17763, row17764, row17765, row17766, row17767, row17768, row17769, row17770, row17771, row17772]

def rows20_9 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17773, row17774, row17775, row17776, row17777, row17778, row17779, row17780, row17781, row17782, row17783, row17784, row17785, row17786, row17787, row17788, row17789, row17790]

def rows20_10 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17791, row17792, row17793, row17794, row17795, row17796, row17797, row17798, row17799, row17800, row17801, row17802, row17803, row17804, row17805, row17806, row17807, row17808]

def rows20_11 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17809, row17810, row17811, row17812, row17813, row17814, row17815, row17816, row17817, row17818, row17819, row17820, row17821, row17822, row17823, row17824, row17825, row17826]

def rows20_12 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17827, row17828, row17829, row17830, row17831, row17832, row17833, row17834, row17835, row17836, row17837, row17838, row17839, row17840, row17841, row17842, row17843, row17844]

def rows20_13 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17845, row17846, row17847, row17848, row17849, row17850, row17851, row17852, row17853, row17854, row17855, row17856, row17857, row17858, row17859, row17860, row17861, row17862]

def rows20_14 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17863, row17864, row17865, row17866, row17867, row17868, row17869, row17870, row17871, row17872, row17873, row17874, row17875, row17876, row17877, row17878, row17879, row17880]

def rows20_15 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17881, row17882, row17883, row17884, row17885, row17886, row17887, row17888, row17889, row17890, row17891, row17892, row17893, row17894, row17895, row17896, row17897, row17898]

def rows20_16 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17899, row17900, row17901, row17902, row17903, row17904, row17905, row17906, row17907, row17908, row17909, row17910, row17911, row17912, row17913, row17914, row17915, row17916]

def rows20_17 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17917, row17918, row17919, row17920, row17921, row17922, row17923, row17924, row17925, row17926, row17927, row17928, row17929, row17930, row17931, row17932, row17933, row17934]

def rows20_18 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17935, row17936, row17937, row17938, row17939, row17940, row17941, row17942, row17943, row17944, row17945, row17946, row17947, row17948, row17949, row17950, row17951, row17952]

def rows20_19 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17953, row17954, row17955, row17956, row17957, row17958, row17959, row17960, row17961, row17962, row17963, row17964, row17965, row17966, row17967, row17968, row17969, row17970]

def rows20_20 : Fin GramFunctions.Block4.form20.size → Integer.Sparse Key := ![row17971, row17972, row17973, row17974, row17975, row17976, row17977, row17978, row17979, row17980, row17981, row17982, row17983, row17984, row17985, row17986, row17987, row17988]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row17989, row17990, row17991, row17992, row17993, row17994, row17995, row17996, row17997, row17998, row17999, row18000, row18001, row18002, row18003, row18004, row18005, row18006, row18007, row18008]

def rows21_1 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18009, row18010, row18011, row18012, row18013, row18014, row18015, row18016, row18017, row18018, row18019, row18020, row18021, row18022, row18023, row18024, row18025, row18026, row18027, row18028]

def rows21_2 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18029, row18030, row18031, row18032, row18033, row18034, row18035, row18036, row18037, row18038, row18039, row18040, row18041, row18042, row18043, row18044, row18045, row18046, row18047, row18048]

def rows21_3 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18049, row18050, row18051, row18052, row18053, row18054, row18055, row18056, row18057, row18058, row18059, row18060, row18061, row18062, row18063, row18064, row18065, row18066, row18067, row18068]

def rows21_4 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18069, row18070, row18071, row18072, row18073, row18074, row18075, row18076, row18077, row18078, row18079, row18080, row18081, row18082, row18083, row18084, row18085, row18086, row18087, row18088]

def rows21_5 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18089, row18090, row18091, row18092, row18093, row18094, row18095, row18096, row18097, row18098, row18099, row18100, row18101, row18102, row18103, row18104, row18105, row18106, row18107, row18108]

def rows21_6 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18109, row18110, row18111, row18112, row18113, row18114, row18115, row18116, row18117, row18118, row18119, row18120, row18121, row18122, row18123, row18124, row18125, row18126, row18127, row18128]

def rows21_7 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18129, row18130, row18131, row18132, row18133, row18134, row18135, row18136, row18137, row18138, row18139, row18140, row18141, row18142, row18143, row18144, row18145, row18146, row18147, row18148]

def rows21_8 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18149, row18150, row18151, row18152, row18153, row18154, row18155, row18156, row18157, row18158, row18159, row18160, row18161, row18162, row18163, row18164, row18165, row18166, row18167, row18168]

def rows21_9 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18169, row18170, row18171, row18172, row18173, row18174, row18175, row18176, row18177, row18178, row18179, row18180, row18181, row18182, row18183, row18184, row18185, row18186, row18187, row18188]

def rows21_10 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18189, row18190, row18191, row18192, row18193, row18194, row18195, row18196, row18197, row18198, row18199, row18200, row18201, row18202, row18203, row18204, row18205, row18206, row18207, row18208]

def rows21_11 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18209, row18210, row18211, row18212, row18213, row18214, row18215, row18216, row18217, row18218, row18219, row18220, row18221, row18222, row18223, row18224, row18225, row18226, row18227, row18228]

def rows21_12 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18229, row18230, row18231, row18232, row18233, row18234, row18235, row18236, row18237, row18238, row18239, row18240, row18241, row18242, row18243, row18244, row18245, row18246, row18247, row18248]

def rows21_13 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18249, row18250, row18251, row18252, row18253, row18254, row18255, row18256, row18257, row18258, row18259, row18260, row18261, row18262, row18263, row18264, row18265, row18266, row18267, row18268]

def rows21_14 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18269, row18270, row18271, row18272, row18273, row18274, row18275, row18276, row18277, row18278, row18279, row18280, row18281, row18282, row18283, row18284, row18285, row18286, row18287, row18288]

def rows21_15 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18289, row18290, row18291, row18292, row18293, row18294, row18295, row18296, row18297, row18298, row18299, row18300, row18301, row18302, row18303, row18304, row18305, row18306, row18307, row18308]

def rows21_16 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18309, row18310, row18311, row18312, row18313, row18314, row18315, row18316, row18317, row18318, row18319, row18320, row18321, row18322, row18323, row18324, row18325, row18326, row18327, row18328]

def rows21_17 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18329, row18330, row18331, row18332, row18333, row18334, row18335, row18336, row18337, row18338, row18339, row18340, row18341, row18342, row18343, row18344, row18345, row18346, row18347, row18348]

def rows21_18 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18349, row18350, row18351, row18352, row18353, row18354, row18355, row18356, row18357, row18358, row18359, row18360, row18361, row18362, row18363, row18364, row18365, row18366, row18367, row18368]

def rows21_19 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18369, row18370, row18371, row18372, row18373, row18374, row18375, row18376, row18377, row18378, row18379, row18380, row18381, row18382, row18383, row18384, row18385, row18386, row18387, row18388]

def rows21_20 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18389, row18390, row18391, row18392, row18393, row18394, row18395, row18396, row18397, row18398, row18399, row18400, row18401, row18402, row18403, row18404, row18405, row18406, row18407, row18408]

def rows21_21 : Fin GramFunctions.Block4.form21.size → Integer.Sparse Key := ![row18409, row18410, row18411, row18412, row18413, row18414, row18415, row18416, row18417, row18418, row18419, row18420, row18421, row18422, row18423, row18424, row18425, row18426, row18427, row18428]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13305, row13306, row13307, row13308, row13309, row13310, row13311, row13312, row13313, row13314, row13315, row13316, row13317, row13318, row13319, row13320, row13321, row13322, row13323, row13324]

def rows3_1 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13325, row13326, row13327, row13328, row13329, row13330, row13331, row13332, row13333, row13334, row13335, row13336, row13337, row13338, row13339, row13340, row13341, row13342, row13343, row13344]

def rows3_2 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13345, row13346, row13347, row13348, row13349, row13350, row13351, row13352, row13353, row13354, row13355, row13356, row13357, row13358, row13359, row13360, row13361, row13362, row13363, row13364]

def rows3_3 : Fin GramFunctions.Block4.form3.size → Integer.Sparse Key := ![row13365, row13366, row13367, row13368, row13369, row13370, row13371, row13372, row13373, row13374, row13375, row13376, row13377, row13378, row13379, row13380, row13381, row13382, row13383, row13384]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13385, row13386, row13387, row13388, row13389, row13390, row13391, row13392, row13393, row13394, row13395, row13396, row13397, row13398, row13399, row13400, row13401, row13402, row13403, row13404]

def rows4_1 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13405, row13406, row13407, row13408, row13409, row13410, row13411, row13412, row13413, row13414, row13415, row13416, row13417, row13418, row13419, row13420, row13421, row13422, row13423, row13424]

def rows4_2 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13425, row13426, row13427, row13428, row13429, row13430, row13431, row13432, row13433, row13434, row13435, row13436, row13437, row13438, row13439, row13440, row13441, row13442, row13443, row13444]

def rows4_3 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13445, row13446, row13447, row13448, row13449, row13450, row13451, row13452, row13453, row13454, row13455, row13456, row13457, row13458, row13459, row13460, row13461, row13462, row13463, row13464]

def rows4_4 : Fin GramFunctions.Block4.form4.size → Integer.Sparse Key := ![row13465, row13466, row13467, row13468, row13469, row13470, row13471, row13472, row13473, row13474, row13475, row13476, row13477, row13478, row13479, row13480, row13481, row13482, row13483, row13484]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13485, row13486, row13487, row13488, row13489, row13490, row13491, row13492, row13493, row13494, row13495, row13496, row13497, row13498, row13499, row13500, row13501, row13502]

def rows5_1 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13503, row13504, row13505, row13506, row13507, row13508, row13509, row13510, row13511, row13512, row13513, row13514, row13515, row13516, row13517, row13518, row13519, row13520]

def rows5_2 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13521, row13522, row13523, row13524, row13525, row13526, row13527, row13528, row13529, row13530, row13531, row13532, row13533, row13534, row13535, row13536, row13537, row13538]

def rows5_3 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13539, row13540, row13541, row13542, row13543, row13544, row13545, row13546, row13547, row13548, row13549, row13550, row13551, row13552, row13553, row13554, row13555, row13556]

def rows5_4 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13557, row13558, row13559, row13560, row13561, row13562, row13563, row13564, row13565, row13566, row13567, row13568, row13569, row13570, row13571, row13572, row13573, row13574]

def rows5_5 : Fin GramFunctions.Block4.form5.size → Integer.Sparse Key := ![row13575, row13576, row13577, row13578, row13579, row13580, row13581, row13582, row13583, row13584, row13585, row13586, row13587, row13588, row13589, row13590, row13591, row13592]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13845, row13846, row13847, row13848, row13849, row13850, row13851, row13852, row13853, row13854]

def rows7_1 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13855, row13856, row13857, row13858, row13859, row13860, row13861, row13862, row13863, row13864]

def rows7_2 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13865, row13866, row13867, row13868, row13869, row13870, row13871, row13872, row13873, row13874]

def rows7_3 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13875, row13876, row13877, row13878, row13879, row13880, row13881, row13882, row13883, row13884]

def rows7_4 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13885, row13886, row13887, row13888, row13889, row13890, row13891, row13892, row13893, row13894]

def rows7_5 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13895, row13896, row13897, row13898, row13899, row13900, row13901, row13902, row13903, row13904]

def rows7_6 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13905, row13906, row13907, row13908, row13909, row13910, row13911, row13912, row13913, row13914]

def rows7_7 : Fin GramFunctions.Block4.form7.size → Integer.Sparse Key := ![row13915, row13916, row13917, row13918, row13919, row13920, row13921, row13922, row13923, row13924]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13925, row13926, row13927, row13928, row13929, row13930, row13931, row13932, row13933, row13934, row13935, row13936, row13937, row13938, row13939, row13940, row13941, row13942, row13943, row13944]

def rows8_1 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13945, row13946, row13947, row13948, row13949, row13950, row13951, row13952, row13953, row13954, row13955, row13956, row13957, row13958, row13959, row13960, row13961, row13962, row13963, row13964]

def rows8_2 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13965, row13966, row13967, row13968, row13969, row13970, row13971, row13972, row13973, row13974, row13975, row13976, row13977, row13978, row13979, row13980, row13981, row13982, row13983, row13984]

def rows8_3 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row13985, row13986, row13987, row13988, row13989, row13990, row13991, row13992, row13993, row13994, row13995, row13996, row13997, row13998, row13999, row14000, row14001, row14002, row14003, row14004]

def rows8_4 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14005, row14006, row14007, row14008, row14009, row14010, row14011, row14012, row14013, row14014, row14015, row14016, row14017, row14018, row14019, row14020, row14021, row14022, row14023, row14024]

def rows8_5 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14025, row14026, row14027, row14028, row14029, row14030, row14031, row14032, row14033, row14034, row14035, row14036, row14037, row14038, row14039, row14040, row14041, row14042, row14043, row14044]

def rows8_6 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14045, row14046, row14047, row14048, row14049, row14050, row14051, row14052, row14053, row14054, row14055, row14056, row14057, row14058, row14059, row14060, row14061, row14062, row14063, row14064]

def rows8_7 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14065, row14066, row14067, row14068, row14069, row14070, row14071, row14072, row14073, row14074, row14075, row14076, row14077, row14078, row14079, row14080, row14081, row14082, row14083, row14084]

def rows8_8 : Fin GramFunctions.Block4.form8.size → Integer.Sparse Key := ![row14085, row14086, row14087, row14088, row14089, row14090, row14091, row14092, row14093, row14094, row14095, row14096, row14097, row14098, row14099, row14100, row14101, row14102, row14103, row14104]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14105, row14106, row14107, row14108, row14109, row14110, row14111, row14112, row14113, row14114]

def rows9_1 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14115, row14116, row14117, row14118, row14119, row14120, row14121, row14122, row14123, row14124]

def rows9_2 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14125, row14126, row14127, row14128, row14129, row14130, row14131, row14132, row14133, row14134]

def rows9_3 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14135, row14136, row14137, row14138, row14139, row14140, row14141, row14142, row14143, row14144]

def rows9_4 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14145, row14146, row14147, row14148, row14149, row14150, row14151, row14152, row14153, row14154]

def rows9_5 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14155, row14156, row14157, row14158, row14159, row14160, row14161, row14162, row14163, row14164]

def rows9_6 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14165, row14166, row14167, row14168, row14169, row14170, row14171, row14172, row14173, row14174]

def rows9_7 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14175, row14176, row14177, row14178, row14179, row14180, row14181, row14182, row14183, row14184]

def rows9_8 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14185, row14186, row14187, row14188, row14189, row14190, row14191, row14192, row14193, row14194]

def rows9_9 : Fin GramFunctions.Block4.form9.size → Integer.Sparse Key := ![row14195, row14196, row14197, row14198, row14199, row14200, row14201, row14202, row14203, row14204]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block5.form0.size → Integer.Sparse Key := ![row18429, row18430, row18431, row18432, row18433, row18434, row18435, row18436, row18437, row18438, row18439, row18440, row18441, row18442, row18443, row18444, row18445, row18446, row18447, row18448]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19384, row19385, row19386, row19387, row19388, row19389, row19390, row19391, row19392, row19393, row19394, row19395, row19396, row19397, row19398, row19399, row19400, row19401, row19402, row19403]

def rows10_1 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19404, row19405, row19406, row19407, row19408, row19409, row19410, row19411, row19412, row19413, row19414, row19415, row19416, row19417, row19418, row19419, row19420, row19421, row19422, row19423]

def rows10_2 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19424, row19425, row19426, row19427, row19428, row19429, row19430, row19431, row19432, row19433, row19434, row19435, row19436, row19437, row19438, row19439, row19440, row19441, row19442, row19443]

def rows10_3 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19444, row19445, row19446, row19447, row19448, row19449, row19450, row19451, row19452, row19453, row19454, row19455, row19456, row19457, row19458, row19459, row19460, row19461, row19462, row19463]

def rows10_4 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19464, row19465, row19466, row19467, row19468, row19469, row19470, row19471, row19472, row19473, row19474, row19475, row19476, row19477, row19478, row19479, row19480, row19481, row19482, row19483]

def rows10_5 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19484, row19485, row19486, row19487, row19488, row19489, row19490, row19491, row19492, row19493, row19494, row19495, row19496, row19497, row19498, row19499, row19500, row19501, row19502, row19503]

def rows10_6 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19504, row19505, row19506, row19507, row19508, row19509, row19510, row19511, row19512, row19513, row19514, row19515, row19516, row19517, row19518, row19519, row19520, row19521, row19522, row19523]

def rows10_7 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19524, row19525, row19526, row19527, row19528, row19529, row19530, row19531, row19532, row19533, row19534, row19535, row19536, row19537, row19538, row19539, row19540, row19541, row19542, row19543]

def rows10_8 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19544, row19545, row19546, row19547, row19548, row19549, row19550, row19551, row19552, row19553, row19554, row19555, row19556, row19557, row19558, row19559, row19560, row19561, row19562, row19563]

def rows10_9 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19564, row19565, row19566, row19567, row19568, row19569, row19570, row19571, row19572, row19573, row19574, row19575, row19576, row19577, row19578, row19579, row19580, row19581, row19582, row19583]

def rows10_10 : Fin GramFunctions.Block5.form10.size → Integer.Sparse Key := ![row19584, row19585, row19586, row19587, row19588, row19589, row19590, row19591, row19592, row19593, row19594, row19595, row19596, row19597, row19598, row19599, row19600, row19601, row19602, row19603]

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

def rows11_0 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19604, row19605, row19606, row19607, row19608, row19609, row19610, row19611, row19612, row19613, row19614, row19615, row19616, row19617, row19618, row19619, row19620, row19621, row19622, row19623, row19624, row19625, row19626, row19627, row19628, row19629, row19630, row19631, row19632, row19633, row19634, row19635, row19636, row19637, row19638, row19639, row19640, row19641, row19642, row19643, row19644, row19645, row19646, row19647, row19648, row19649, row19650, row19651, row19652, row19653, row19654, row19655, row19656, row19657, row19658, row19659, row19660, row19661, row19662, row19663]

def rows11_1 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19664, row19665, row19666, row19667, row19668, row19669, row19670, row19671, row19672, row19673, row19674, row19675, row19676, row19677, row19678, row19679, row19680, row19681, row19682, row19683, row19684, row19685, row19686, row19687, row19688, row19689, row19690, row19691, row19692, row19693, row19694, row19695, row19696, row19697, row19698, row19699, row19700, row19701, row19702, row19703, row19704, row19705, row19706, row19707, row19708, row19709, row19710, row19711, row19712, row19713, row19714, row19715, row19716, row19717, row19718, row19719, row19720, row19721, row19722, row19723]

def rows11_10 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20204, row20205, row20206, row20207, row20208, row20209, row20210, row20211, row20212, row20213, row20214, row20215, row20216, row20217, row20218, row20219, row20220, row20221, row20222, row20223, row20224, row20225, row20226, row20227, row20228, row20229, row20230, row20231, row20232, row20233, row20234, row20235, row20236, row20237, row20238, row20239, row20240, row20241, row20242, row20243, row20244, row20245, row20246, row20247, row20248, row20249, row20250, row20251, row20252, row20253, row20254, row20255, row20256, row20257, row20258, row20259, row20260, row20261, row20262, row20263]

end MUB6.Certificate.GramEntries.Block5

end OAI
end


