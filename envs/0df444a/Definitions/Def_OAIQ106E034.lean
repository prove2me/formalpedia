-- Prove2me | Definitions.Def_OAIQ106E034
-- name    : OAIQ106E034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:55:08.760057+00:00
-- url     : https://prove2.me/theorems/1a6c7ac8-c5f0-4063-bf56-cddcb3d050db
-- title:
--   Definitions bundle OAIQ106E034 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 89 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.rows8_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows8_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows8_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows8_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_4`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_5`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_6`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_7`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_8`, `OAI.MUB6.Certificate.GramEntries.Block4.rows10_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_11`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_4`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_5`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_6`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_7`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_8`, `OAI.MUB6.Certificate.GramEntries.Block4.rows11_9`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_0`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_1`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_10`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_11`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_12`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_2`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_3`, `OAI.MUB6.Certificate.GramEntries.Block4.rows12_4` and 49 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row8.lean), [`MutuallyUnbiased_GramEntries_Block3Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row9.lean), [`MutuallyUnbiased_GramEntries_Block4Row0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row0.lean), [`MutuallyUnbiased_GramEntries_Block4Row10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row10.lean), [`MutuallyUnbiased_GramEntries_Block4Row11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row11.lean), [`MutuallyUnbiased_GramEntries_Block4Row12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row12.lean), [`MutuallyUnbiased_GramEntries_Block4Row13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row13.lean), [`MutuallyUnbiased_GramEntries_Block4Row14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row14.lean), [`MutuallyUnbiased_GramEntries_Block4Row15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Row15.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E032` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval12_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E032

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_4 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8089, row8090, row8091, row8092, row8093, row8094, row8095, row8096, row8097, row8098, row8099, row8100, row8101, row8102, row8103, row8104, row8105, row8106, row8107, row8108, row8109, row8110, row8111, row8112, row8113, row8114, row8115, row8116, row8117, row8118, row8119, row8120, row8121, row8122, row8123, row8124]

def rows8_5 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8125, row8126, row8127, row8128, row8129, row8130, row8131, row8132, row8133, row8134, row8135, row8136, row8137, row8138, row8139, row8140, row8141, row8142, row8143, row8144, row8145, row8146, row8147, row8148, row8149, row8150, row8151, row8152, row8153, row8154, row8155, row8156, row8157, row8158, row8159, row8160]

def rows8_7 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8197, row8198, row8199, row8200, row8201, row8202, row8203, row8204, row8205, row8206, row8207, row8208, row8209, row8210, row8211, row8212, row8213, row8214, row8215, row8216, row8217, row8218, row8219, row8220, row8221, row8222, row8223, row8224, row8225, row8226, row8227, row8228, row8229, row8230, row8231, row8232]

def rows8_8 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8233, row8234, row8235, row8236, row8237, row8238, row8239, row8240, row8241, row8242, row8243, row8244, row8245, row8246, row8247, row8248, row8249, row8250, row8251, row8252, row8253, row8254, row8255, row8256, row8257, row8258, row8259, row8260, row8261, row8262, row8263, row8264, row8265, row8266, row8267, row8268]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_6 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8341, row8342, row8343, row8344, row8345, row8346, row8347, row8348, row8349, row8350, row8351, row8352, row8353, row8354, row8355, row8356, row8357, row8358, row8359, row8360, row8361, row8362, row8363, row8364, row8365, row8366, row8367, row8368, row8369, row8370, row8371, row8372, row8373, row8374, row8375, row8376]

def rows9_7 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8377, row8378, row8379, row8380, row8381, row8382, row8383, row8384, row8385, row8386, row8387, row8388, row8389, row8390, row8391, row8392, row8393, row8394, row8395, row8396, row8397, row8398, row8399, row8400, row8401, row8402, row8403, row8404, row8405, row8406, row8407, row8408, row8409, row8410, row8411, row8412]

def rows9_8 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8413, row8414, row8415, row8416, row8417, row8418, row8419, row8420, row8421, row8422, row8423, row8424, row8425, row8426, row8427, row8428, row8429, row8430, row8431, row8432, row8433, row8434, row8435, row8436, row8437, row8438, row8439, row8440, row8441, row8442, row8443, row8444, row8445, row8446, row8447, row8448]

def rows9_9 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8449, row8450, row8451, row8452, row8453, row8454, row8455, row8456, row8457, row8458, row8459, row8460, row8461, row8462, row8463, row8464, row8465, row8466, row8467, row8468, row8469, row8470, row8471, row8472, row8473, row8474, row8475, row8476, row8477, row8478, row8479, row8480, row8481, row8482, row8483, row8484]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block4.form0.size → Integer.Sparse Key := ![row13187, row13188, row13189, row13190, row13191, row13192, row13193, row13194, row13195, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row14214, row14215, row14216, row14217, row14218, row14219, row14220, row14221, row14222, row14223, row14224, row14225, row14226, row14227, row14228, row14229, row14230, row14231, row14232, row14233, row14234, row14235, row14236, row14237, row14238, row14239, row14240]

def rows10_1 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row14250, row14251, row14252, row14253, row14254, row14255, row14256, row14257, row14258, row14259, row14260, row14261, row14262, row14263, row14264, row14265, row14266, row14267, row14268, row14269, row14270, row14271, row14272, row14273, row14274, row14275, row14276]

def rows10_2 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row14286, row14287, row14288, row14289, row14290, row14291, row14292, row14293, row14294, row14295, row14296, row14297, row14298, row14299, row14300, row14301, row14302, row14303, row14304, row14305, row14306, row14307, row14308, row14309, row14310, row14311, row14312]

def rows10_3 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row14322, row14323, row14324, row14325, row14326, row14327, row14328, row14329, row14330, row14331, row14332, row14333, row14334, row14335, row14336, row14337, row14338, row14339, row14340, row14341, row14342, row14343, row14344, row14345, row14346, row14347, row14348]

def rows10_4 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row14358, row14359, row14360, row14361, row14362, row14363, row14364, row14365, row14366, row14367, row14368, row14369, row14370, row14371, row14372, row14373, row14374, row14375, row14376, row14377, row14378, row14379, row14380, row14381, row14382, row14383, row14384]

def rows10_5 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row14394, row14395, row14396, row14397, row14398, row14399, row14400, row14401, row14402, row14403, row14404, row14405, row14406, row14407, row14408, row14409, row14410, row14411, row14412, row14413, row14414, row14415, row14416, row14417, row14418, row14419, row14420]

def rows10_6 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row14430, row14431, row14432, row14433, row14434, row14435, row14436, row14437, row14438, row14439, row14440, row14441, row14442, row14443, row14444, row14445, row14446, row14447, row14448, row14449, row14450, row14451, row14452, row14453, row14454, row14455, row14456]

def rows10_7 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row14466, row14467, row14468, row14469, row14470, row14471, row14472, row14473, row14474, row14475, row14476, row14477, row14478, row14479, row14480, row14481, row14482, row14483, row14484, row14485, row14486, row14487, row14488, row14489, row14490, row14491, row14492]

def rows10_8 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row14502, row14503, row14504, row14505, row14506, row14507, row14508, row14509, row14510, row14511, row14512, row14513, row14514, row14515, row14516, row14517, row14518, row14519, row14520, row14521, row14522, row14523, row14524, row14525, row14526, row14527, row14528]

def rows10_9 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row14538, row14539, row14540, row14541, row14542, row14543, row14544, row14545, row14546, row14547, row14548, row14549, row14550, row14551, row14552, row14553, row14554, row14555, row14556, row14557, row14558, row14559, row14560, row14561, row14562, row14563, row14564]

def rows10_10 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row14574, row14575, row14576, row14577, row14578, row14579, row14580, row14581, row14582, row14583, row14584, row14585, row14586, row14587, row14588, row14589, row14590, row14591, row14592, row14593, row14594, row14595, row14596, row14597, row14598, row14599, row14600]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14601, row14602, row14603, row14604, row14605, row14606, row14607, row14608, row14609, row14610, row14611, row14612, row14613, row14614, row14615, row14616, row14617, row14618, row14619, row14620]

def rows11_1 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14621, row14622, row14623, row14624, row14625, row14626, row14627, row14628, row14629, row14630, row14631, row14632, row14633, row14634, row14635, row14636, row14637, row14638, row14639, row14640]

def rows11_2 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14641, row14642, row14643, row14644, row14645, row14646, row14647, row14648, row14649, row14650, row14651, row14652, row14653, row14654, row14655, row14656, row14657, row14658, row14659, row14660]

def rows11_3 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14661, row14662, row14663, row14664, row14665, row14666, row14667, row14668, row14669, row14670, row14671, row14672, row14673, row14674, row14675, row14676, row14677, row14678, row14679, row14680]

def rows11_4 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14681, row14682, row14683, row14684, row14685, row14686, row14687, row14688, row14689, row14690, row14691, row14692, row14693, row14694, row14695, row14696, row14697, row14698, row14699, row14700]

def rows11_5 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14701, row14702, row14703, row14704, row14705, row14706, row14707, row14708, row14709, row14710, row14711, row14712, row14713, row14714, row14715, row14716, row14717, row14718, row14719, row14720]

def rows11_6 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14721, row14722, row14723, row14724, row14725, row14726, row14727, row14728, row14729, row14730, row14731, row14732, row14733, row14734, row14735, row14736, row14737, row14738, row14739, row14740]

def rows11_7 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14741, row14742, row14743, row14744, row14745, row14746, row14747, row14748, row14749, row14750, row14751, row14752, row14753, row14754, row14755, row14756, row14757, row14758, row14759, row14760]

def rows11_8 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14761, row14762, row14763, row14764, row14765, row14766, row14767, row14768, row14769, row14770, row14771, row14772, row14773, row14774, row14775, row14776, row14777, row14778, row14779, row14780]

def rows11_9 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14781, row14782, row14783, row14784, row14785, row14786, row14787, row14788, row14789, row14790, row14791, row14792, row14793, row14794, row14795, row14796, row14797, row14798, row14799, row14800]

def rows11_10 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14801, row14802, row14803, row14804, row14805, row14806, row14807, row14808, row14809, row14810, row14811, row14812, row14813, row14814, row14815, row14816, row14817, row14818, row14819, row14820]

def rows11_11 : Fin GramFunctions.Block4.form11.size → Integer.Sparse Key := ![row14821, row14822, row14823, row14824, row14825, row14826, row14827, row14828, row14829, row14830, row14831, row14832, row14833, row14834, row14835, row14836, row14837, row14838, row14839, row14840]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14841, row14842, row14843, row14844, row14845, row14846, row14847, row14848, row14849, row13190, row13191, row13192, row13193, row13194, row13195, row14850, row14851, row14852, row13196, row13197, row13198, row13199, row13200, row13201, row13202, row13203, row13204]

def rows12_1 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14853, row14854, row14855, row14856, row14857, row14858, row14859, row14860, row14861, row14862, row14863, row14864, row14865, row14866, row14867, row14868, row14869, row14870, row14871, row14872, row14873, row14874, row14875, row14876, row14877, row14878, row14879]

def rows12_2 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14880, row14881, row14882, row14883, row14884, row14885, row14886, row14887, row14888, row14889, row14890, row14891, row14892, row14893, row14894, row14895, row14896, row14897, row14898, row14899, row14900, row14901, row14902, row14903, row14904, row14905, row14906]

def rows12_3 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14907, row14908, row14909, row14910, row14911, row14912, row14913, row14914, row14915, row14916, row14917, row14918, row14919, row14920, row14921, row14922, row14923, row14924, row14925, row14926, row14927, row14928, row14929, row14930, row14931, row14932, row14933]

def rows12_4 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14934, row14935, row14936, row14937, row14938, row14939, row14940, row14941, row14942, row14943, row14944, row14945, row14946, row14947, row14948, row14949, row14950, row14951, row14952, row14953, row14954, row14955, row14956, row14957, row14958, row14959, row14960]

def rows12_5 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14961, row14962, row14963, row14964, row14965, row14966, row14967, row14968, row14969, row14970, row14971, row14972, row14973, row14974, row14975, row14976, row14977, row14978, row14979, row14980, row14981, row14982, row14983, row14984, row14985, row14986, row14987]

def rows12_6 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row14988, row14989, row14990, row14991, row14992, row14993, row14994, row14995, row14996, row14997, row14998, row14999, row15000, row15001, row15002, row15003, row15004, row15005, row15006, row15007, row15008, row15009, row15010, row15011, row15012, row15013, row15014]

def rows12_7 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15015, row15016, row15017, row15018, row15019, row15020, row15021, row15022, row15023, row15024, row15025, row15026, row15027, row15028, row15029, row15030, row15031, row15032, row15033, row15034, row15035, row15036, row15037, row15038, row15039, row15040, row15041]

def rows12_8 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15042, row15043, row15044, row15045, row15046, row15047, row15048, row15049, row15050, row15051, row15052, row15053, row15054, row15055, row15056, row15057, row15058, row15059, row15060, row15061, row15062, row15063, row15064, row15065, row15066, row15067, row15068]

def rows12_9 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15069, row15070, row15071, row15072, row15073, row15074, row15075, row15076, row15077, row15078, row15079, row15080, row15081, row15082, row15083, row15084, row15085, row15086, row15087, row15088, row15089, row15090, row15091, row15092, row15093, row15094, row15095]

def rows12_10 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15096, row15097, row15098, row15099, row15100, row15101, row15102, row15103, row15104, row15105, row15106, row15107, row15108, row15109, row15110, row15111, row15112, row15113, row15114, row15115, row15116, row15117, row15118, row15119, row15120, row15121, row15122]

def rows12_11 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15123, row15124, row15125, row15126, row15127, row15128, row15129, row15130, row15131, row15132, row15133, row15134, row15135, row15136, row15137, row15138, row15139, row15140, row15141, row15142, row15143, row15144, row15145, row15146, row15147, row15148, row15149]

def rows12_12 : Fin GramFunctions.Block4.form12.size → Integer.Sparse Key := ![row15150, row15151, row15152, row15153, row15154, row15155, row15156, row15157, row15158, row15159, row15160, row15161, row15162, row15163, row15164, row15165, row15166, row15167, row15168, row15169, row15170, row15171, row15172, row15173, row15174, row15175, row15176]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15177, row15178, row15179, row15180, row15181, row15182, row15183, row15184, row15185, row15186, row15187, row15188, row13593, row13594, row13595, row13596, row13597, row13598, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row13608, row13609, row13610, row13611, row13612, row13613]

def rows13_1 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15195, row15196, row15197, row15198, row15199, row15200, row15201, row15202, row15203, row15204, row15205, row15206, row13629, row13630, row13631, row13632, row13633, row13634, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row13644, row13645, row13646, row13647, row13648, row13649]

def rows13_2 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15213, row15214, row15215, row15216, row15217, row15218, row15219, row15220, row15221, row15222, row15223, row15224, row13665, row13666, row13667, row13668, row13669, row13670, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row13680, row13681, row13682, row13683, row13684, row13685]

def rows13_3 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15231, row15232, row15233, row15234, row15235, row15236, row15237, row15238, row15239, row15240, row15241, row15242, row13701, row13702, row13703, row13704, row13705, row13706, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row13716, row13717, row13718, row13719, row13720, row13721]

def rows13_4 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15249, row15250, row15251, row15252, row15253, row15254, row15255, row15256, row15257, row15258, row15259, row15260, row13737, row13738, row13739, row13740, row13741, row13742, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row13752, row13753, row13754, row13755, row13756, row13757]

def rows13_5 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15267, row15268, row15269, row15270, row15271, row15272, row15273, row15274, row15275, row15276, row15277, row15278, row13773, row13774, row13775, row13776, row13777, row13778, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row13788, row13789, row13790, row13791, row13792, row13793]

def rows13_6 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15285, row15286, row15287, row15288, row15289, row15290, row15291, row15292, row15293, row15294, row15295, row15296, row13809, row13810, row13811, row13812, row13813, row13814, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row13824, row13825, row13826, row13827, row13828, row13829]

def rows13_7 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15303, row15304, row15305, row15306, row15307, row15308, row15309, row15310, row15311, row15312, row15313, row15314, row15315, row15316, row15317, row15318, row15319, row15320, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15333, row15334, row15335, row15336, row15337, row15338]

def rows13_8 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15339, row15340, row15341, row15342, row15343, row15344, row15345, row15346, row15347, row15348, row15349, row15350, row15351, row15352, row15353, row15354, row15355, row15356, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15369, row15370, row15371, row15372, row15373, row15374]

def rows13_9 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15375, row15376, row15377, row15378, row15379, row15380, row15381, row15382, row15383, row15384, row15385, row15386, row15387, row15388, row15389, row15390, row15391, row15392, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15405, row15406, row15407, row15408, row15409, row15410]

def rows13_10 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15411, row15412, row15413, row15414, row15415, row15416, row15417, row15418, row15419, row15420, row15421, row15422, row15423, row15424, row15425, row15426, row15427, row15428, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15441, row15442, row15443, row15444, row15445, row15446]

def rows13_11 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15447, row15448, row15449, row15450, row15451, row15452, row15453, row15454, row15455, row15456, row15457, row15458, row15459, row15460, row15461, row15462, row15463, row15464, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15477, row15478, row15479, row15480, row15481, row15482]

def rows13_12 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15483, row15484, row15485, row15486, row15487, row15488, row15489, row15490, row15491, row15492, row15493, row15494, row15495, row15496, row15497, row15498, row15499, row15500, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15513, row15514, row15515, row15516, row15517, row15518]

def rows13_13 : Fin GramFunctions.Block4.form13.size → Integer.Sparse Key := ![row15519, row15520, row15521, row15522, row15523, row15524, row15525, row15526, row15527, row15528, row15529, row15530, row15531, row15532, row15533, row15534, row15535, row15536, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15549, row15550, row15551, row15552, row15553, row15554]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15180, row15181, row15182, row15183, row15184, row15185, row15555, row15556, row15557, row13593, row13594, row13595, row13596, row13597, row13598, row13599, row13600, row13601, row15189, row15190, row15191, row15192, row15193, row15194, row13602, row13603, row13604, row13605, row13606, row13607, row15558, row15559, row15560, row13620, row13621, row13622]

def rows14_1 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15198, row15199, row15200, row15201, row15202, row15203, row15561, row15562, row15563, row13629, row13630, row13631, row13632, row13633, row13634, row13635, row13636, row13637, row15207, row15208, row15209, row15210, row15211, row15212, row13638, row13639, row13640, row13641, row13642, row13643, row15564, row15565, row15566, row13656, row13657, row13658]

def rows14_2 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15216, row15217, row15218, row15219, row15220, row15221, row15567, row15568, row15569, row13665, row13666, row13667, row13668, row13669, row13670, row13671, row13672, row13673, row15225, row15226, row15227, row15228, row15229, row15230, row13674, row13675, row13676, row13677, row13678, row13679, row15570, row15571, row15572, row13692, row13693, row13694]

def rows14_3 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15234, row15235, row15236, row15237, row15238, row15239, row15573, row15574, row15575, row13701, row13702, row13703, row13704, row13705, row13706, row13707, row13708, row13709, row15243, row15244, row15245, row15246, row15247, row15248, row13710, row13711, row13712, row13713, row13714, row13715, row15576, row15577, row15578, row13728, row13729, row13730]

def rows14_4 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15252, row15253, row15254, row15255, row15256, row15257, row15579, row15580, row15581, row13737, row13738, row13739, row13740, row13741, row13742, row13743, row13744, row13745, row15261, row15262, row15263, row15264, row15265, row15266, row13746, row13747, row13748, row13749, row13750, row13751, row15582, row15583, row15584, row13764, row13765, row13766]

def rows14_5 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15270, row15271, row15272, row15273, row15274, row15275, row15585, row15586, row15587, row13773, row13774, row13775, row13776, row13777, row13778, row13779, row13780, row13781, row15279, row15280, row15281, row15282, row15283, row15284, row13782, row13783, row13784, row13785, row13786, row13787, row15588, row15589, row15590, row13800, row13801, row13802]

def rows14_6 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15288, row15289, row15290, row15291, row15292, row15293, row15591, row15592, row15593, row13809, row13810, row13811, row13812, row13813, row13814, row13815, row13816, row13817, row15297, row15298, row15299, row15300, row15301, row15302, row13818, row13819, row13820, row13821, row13822, row13823, row15594, row15595, row15596, row13836, row13837, row13838]

def rows14_7 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15306, row15307, row15308, row15309, row15310, row15311, row15597, row15598, row15599, row15315, row15316, row15317, row15318, row15319, row15320, row15600, row15601, row15602, row15321, row15322, row15323, row15324, row15325, row15326, row15327, row15328, row15329, row15330, row15331, row15332, row15603, row15604, row15605, row15606, row15607, row15608]

def rows14_8 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15342, row15343, row15344, row15345, row15346, row15347, row15609, row15610, row15611, row15351, row15352, row15353, row15354, row15355, row15356, row15612, row15613, row15614, row15357, row15358, row15359, row15360, row15361, row15362, row15363, row15364, row15365, row15366, row15367, row15368, row15615, row15616, row15617, row15618, row15619, row15620]

def rows14_9 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15378, row15379, row15380, row15381, row15382, row15383, row15621, row15622, row15623, row15387, row15388, row15389, row15390, row15391, row15392, row15624, row15625, row15626, row15393, row15394, row15395, row15396, row15397, row15398, row15399, row15400, row15401, row15402, row15403, row15404, row15627, row15628, row15629, row15630, row15631, row15632]

def rows14_10 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15414, row15415, row15416, row15417, row15418, row15419, row15633, row15634, row15635, row15423, row15424, row15425, row15426, row15427, row15428, row15636, row15637, row15638, row15429, row15430, row15431, row15432, row15433, row15434, row15435, row15436, row15437, row15438, row15439, row15440, row15639, row15640, row15641, row15642, row15643, row15644]

def rows14_11 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15450, row15451, row15452, row15453, row15454, row15455, row15645, row15646, row15647, row15459, row15460, row15461, row15462, row15463, row15464, row15648, row15649, row15650, row15465, row15466, row15467, row15468, row15469, row15470, row15471, row15472, row15473, row15474, row15475, row15476, row15651, row15652, row15653, row15654, row15655, row15656]

def rows14_12 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15486, row15487, row15488, row15489, row15490, row15491, row15657, row15658, row15659, row15495, row15496, row15497, row15498, row15499, row15500, row15660, row15661, row15662, row15501, row15502, row15503, row15504, row15505, row15506, row15507, row15508, row15509, row15510, row15511, row15512, row15663, row15664, row15665, row15666, row15667, row15668]

def rows14_13 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15522, row15523, row15524, row15525, row15526, row15527, row15669, row15670, row15671, row15531, row15532, row15533, row15534, row15535, row15536, row15672, row15673, row15674, row15537, row15538, row15539, row15540, row15541, row15542, row15543, row15544, row15545, row15546, row15547, row15548, row15675, row15676, row15677, row15678, row15679, row15680]

def rows14_14 : Fin GramFunctions.Block4.form14.size → Integer.Sparse Key := ![row15681, row15682, row15683, row15684, row15685, row15686, row15687, row15688, row15689, row15690, row15691, row15692, row15693, row15694, row15695, row15696, row15697, row15698, row15699, row15700, row15701, row15702, row15703, row15704, row15705, row15706, row15707, row15708, row15709, row15710, row15711, row15712, row15713, row15714, row15715, row15716]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

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

def rows15_0 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15717, row15718, row15719, row15720, row15721, row15722, row15723, row15724, row15725, row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row15726, row15727, row15728, row15729, row15730, row15731, row14214, row14215, row14216, row14217, row14218, row14219, row15732, row15733, row15734, row14232, row14233, row14234]

def rows15_1 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15735, row15736, row15737, row15738, row15739, row15740, row15741, row15742, row15743, row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row15744, row15745, row15746, row15747, row15748, row15749, row14250, row14251, row14252, row14253, row14254, row14255, row15750, row15751, row15752, row14268, row14269, row14270]

def rows15_2 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15753, row15754, row15755, row15756, row15757, row15758, row15759, row15760, row15761, row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row15762, row15763, row15764, row15765, row15766, row15767, row14286, row14287, row14288, row14289, row14290, row14291, row15768, row15769, row15770, row14304, row14305, row14306]

def rows15_3 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15771, row15772, row15773, row15774, row15775, row15776, row15777, row15778, row15779, row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row15780, row15781, row15782, row15783, row15784, row15785, row14322, row14323, row14324, row14325, row14326, row14327, row15786, row15787, row15788, row14340, row14341, row14342]

def rows15_4 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15789, row15790, row15791, row15792, row15793, row15794, row15795, row15796, row15797, row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row15798, row15799, row15800, row15801, row15802, row15803, row14358, row14359, row14360, row14361, row14362, row14363, row15804, row15805, row15806, row14376, row14377, row14378]

def rows15_5 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15807, row15808, row15809, row15810, row15811, row15812, row15813, row15814, row15815, row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row15816, row15817, row15818, row15819, row15820, row15821, row14394, row14395, row14396, row14397, row14398, row14399, row15822, row15823, row15824, row14412, row14413, row14414]

def rows15_6 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15825, row15826, row15827, row15828, row15829, row15830, row15831, row15832, row15833, row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row15834, row15835, row15836, row15837, row15838, row15839, row14430, row14431, row14432, row14433, row14434, row14435, row15840, row15841, row15842, row14448, row14449, row14450]

def rows15_7 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15843, row15844, row15845, row15846, row15847, row15848, row15849, row15850, row15851, row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row15852, row15853, row15854, row15855, row15856, row15857, row14466, row14467, row14468, row14469, row14470, row14471, row15858, row15859, row15860, row14484, row14485, row14486]

def rows15_8 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15861, row15862, row15863, row15864, row15865, row15866, row15867, row15868, row15869, row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row15870, row15871, row15872, row15873, row15874, row15875, row14502, row14503, row14504, row14505, row14506, row14507, row15876, row15877, row15878, row14520, row14521, row14522]

def rows15_10 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15897, row15898, row15899, row15900, row15901, row15902, row15903, row15904, row15905, row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row15906, row15907, row15908, row15909, row15910, row15911, row14574, row14575, row14576, row14577, row14578, row14579, row15912, row15913, row15914, row14592, row14593, row14594]

def rows15_11 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15915, row15916, row15917, row15918, row15919, row15920, row15921, row15922, row15923, row15924, row15925, row15926, row15927, row15928, row15929, row15930, row15931, row15932, row15933, row15934, row15935, row15936, row15937, row15938, row15939, row15940, row15941, row15942, row15943, row15944, row15945, row15946, row15947, row15948, row15949, row15950]

def rows15_12 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15951, row15952, row15953, row15954, row15955, row15956, row15957, row15958, row15959, row15960, row15961, row15962, row15963, row15964, row15965, row15966, row15967, row15968, row15969, row15970, row15971, row15972, row15973, row15974, row15975, row15976, row15977, row15978, row15979, row15980, row15981, row15982, row15983, row15984, row15985, row15986]

def rows15_13 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row15987, row15988, row15989, row15990, row15991, row15992, row15993, row15994, row15995, row15996, row15997, row15998, row15999, row16000, row16001, row16002, row16003, row16004, row16005, row16006, row16007, row16008, row16009, row16010, row16011, row16012, row16013, row16014, row16015, row16016, row16017, row16018, row16019, row16020, row16021, row16022]

def rows15_14 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16023, row16024, row16025, row16026, row16027, row16028, row16029, row16030, row16031, row16032, row16033, row16034, row16035, row16036, row16037, row16038, row16039, row16040, row16041, row16042, row16043, row16044, row16045, row16046, row16047, row16048, row16049, row16050, row16051, row16052, row16053, row16054, row16055, row16056, row16057, row16058]

def rows15_15 : Fin GramFunctions.Block4.form15.size → Integer.Sparse Key := ![row16059, row16060, row16061, row16062, row16063, row16064, row16065, row16066, row16067, row16068, row16069, row16070, row16071, row16072, row16073, row16074, row16075, row16076, row16077, row16078, row16079, row16080, row16081, row16082, row16083, row16084, row16085, row16086, row16087, row16088, row16089, row16090, row16091, row16092, row16093, row16094]

end MUB6.Certificate.GramEntries.Block4

end OAI
end


