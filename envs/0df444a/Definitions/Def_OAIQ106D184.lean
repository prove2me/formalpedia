-- Prove2me | Definitions.Def_OAIQ106D184
-- name    : OAIQ106D184
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:44:15.564737+00:00
-- url     : https://prove2.me/theorems/8af6c709-d230-45ff-8523-9f4b850ccc38
-- title:
--   Definitions bundle OAIQ106D184 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 658 declarations of OpenAI's Lean: 658 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow790`, `OAI.MUB6.Certificate.GramRows.rawRow7904`, `OAI.MUB6.Certificate.GramRows.rawRow7905`, `OAI.MUB6.Certificate.GramRows.rawRow7906`, `OAI.MUB6.Certificate.GramRows.rawRow7907`, `OAI.MUB6.Certificate.GramRows.rawRow7908`, `OAI.MUB6.Certificate.GramRows.rawRow7909`, `OAI.MUB6.Certificate.GramRows.rawRow791`, `OAI.MUB6.Certificate.GramRows.rawRow7910`, `OAI.MUB6.Certificate.GramRows.rawRow7911`, `OAI.MUB6.Certificate.GramRows.rawRow7912`, `OAI.MUB6.Certificate.GramRows.rawRow7913`, `OAI.MUB6.Certificate.GramRows.rawRow7914`, `OAI.MUB6.Certificate.GramRows.rawRow7915`, `OAI.MUB6.Certificate.GramRows.rawRow7916`, `OAI.MUB6.Certificate.GramRows.rawRow7917`, `OAI.MUB6.Certificate.GramRows.rawRow7918`, `OAI.MUB6.Certificate.GramRows.rawRow7919`, `OAI.MUB6.Certificate.GramRows.rawRow792`, `OAI.MUB6.Certificate.GramRows.rawRow7920`, `OAI.MUB6.Certificate.GramRows.rawRow793`, `OAI.MUB6.Certificate.GramRows.rawRow794`, `OAI.MUB6.Certificate.GramRows.rawRow796`, `OAI.MUB6.Certificate.GramRows.rawRow797`, `OAI.MUB6.Certificate.GramRows.rawRow798`, `OAI.MUB6.Certificate.GramRows.rawRow7981`, `OAI.MUB6.Certificate.GramRows.rawRow7982`, `OAI.MUB6.Certificate.GramRows.rawRow7983`, `OAI.MUB6.Certificate.GramRows.rawRow7984`, `OAI.MUB6.Certificate.GramRows.rawRow7985`, `OAI.MUB6.Certificate.GramRows.rawRow7986`, `OAI.MUB6.Certificate.GramRows.rawRow7987`, `OAI.MUB6.Certificate.GramRows.rawRow7988`, `OAI.MUB6.Certificate.GramRows.rawRow7989`, `OAI.MUB6.Certificate.GramRows.rawRow799`, `OAI.MUB6.Certificate.GramRows.rawRow7990`, `OAI.MUB6.Certificate.GramRows.rawRow7991`, `OAI.MUB6.Certificate.GramRows.rawRow7992`, `OAI.MUB6.Certificate.GramRows.rawRow7993`, `OAI.MUB6.Certificate.GramRows.rawRow7994` and 618 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block22`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block24`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block87`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block91`, `MutuallyUnbiased_TaoCertificate_Merge25`.
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key267, 2), (key251, 1), (key260, 1), (key239, -1), (key251, -1), (key248, -2), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key328, -2), (key319, -1), (key335, -1), (key305, 1), (key319, 1), (key316, 2), (key302, -1), (key316, -1), (key450, -1), (key475, -1), (key418, 1), (key450, 1), (key442, 1), (key469, 1), (key397, -1), (key442, -1), (key406, -1), (key435, -1), (key385, 1), (key435, 1), (key601, 2), (key583, -1), (key601, -1), (key595, -2), (key572, 1), (key595, 1), (key578, 1), (key593, 1), (key568, -1), (key593, -1)]

def rawRow80 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1825, 2), (key1772, 1), (key1780, 1), (key1798, -1), (key1844, -1), (key1774, -2), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1667, -2), (key1337, -1), (key1345, -1), (key1466, 1), (key1844, 1), (key1339, 2), (key1457, -1), (key1839, -1), (key1546, -1), (key1559, -1), (key1596, 1), (key1667, 1), (key1316, 1), (key1329, 1), (key1447, -1), (key1825, -1), (key1302, -1), (key1339, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1573, -1), (key1655, -1), (key1316, -2), (key1424, 1), (key1813, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

def rawRow81 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1825, 2), (key1780, 1), (key1772, 1), (key1844, -1), (key1798, -1), (key1774, -2), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1667, -2), (key1345, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1339, 2), (key1839, -1), (key1457, -1), (key1559, -1), (key1546, -1), (key1667, 1), (key1596, 1), (key1329, 1), (key1316, 1), (key1825, -1), (key1447, -1), (key1339, -1), (key1302, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1655, -1), (key1573, -1), (key1316, -2), (key1813, 1), (key1424, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

def rawRow82 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1817, 2), (key1788, 1), (key1798, 1), (key1780, -1), (key1841, -1), (key1790, -2), (key1774, 1), (key1839, 1), (key1655, 1), (key1667, 1), (key1659, -2), (key1455, -1), (key1466, -1), (key1345, 1), (key1841, 1), (key1457, 2), (key1339, -1), (key1839, -1), (key1573, -1), (key1596, -1), (key1559, 1), (key1659, 1), (key1424, 1), (key1447, 1), (key1329, -1), (key1817, -1), (key1397, -1), (key1457, -1), (key1302, 1), (key1790, 1), (key1573, 2), (key1546, -1), (key1655, -1), (key1424, -2), (key1316, 1), (key1813, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

def rawRow83 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1817, 2), (key1798, 1), (key1788, 1), (key1841, -1), (key1780, -1), (key1790, -2), (key1839, 1), (key1774, 1), (key1667, 1), (key1655, 1), (key1659, -2), (key1466, -1), (key1455, -1), (key1841, 1), (key1345, 1), (key1457, 2), (key1839, -1), (key1339, -1), (key1596, -1), (key1573, -1), (key1659, 1), (key1559, 1), (key1447, 1), (key1424, 1), (key1817, -1), (key1329, -1), (key1457, -1), (key1397, -1), (key1790, 1), (key1302, 1), (key1573, 2), (key1655, -1), (key1546, -1), (key1424, -2), (key1813, 1), (key1316, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

def rawRow85 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2655, -1), (key2656, -1), (key2650, 1), (key2656, 1), (key2675, 2), (key2672, -1), (key2675, -1), (key2730, -2), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2739, -1), (key2751, -1), (key2797, -2), (key2787, 1), (key2797, 1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, 1), (key2915, 1), (key2945, 1), (key2946, 1), (key2940, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2952, 1), (key2964, 1), (key2985, 1), (key2994, 1), (key2978, -1), (key2994, -1)]

def rawRow86 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2656, -1), (key2655, -1), (key2656, 1), (key2650, 1), (key2675, 2), (key2675, -1), (key2672, -1), (key2730, -2), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2751, -1), (key2739, -1), (key2797, -2), (key2797, 1), (key2787, 1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2899, 1), (key2946, 1), (key2945, 1), (key2946, -1), (key2940, -1), (key2964, -1), (key2962, -1), (key2964, 1), (key2952, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2978, -1)]

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

def rawRow790 : Integer.Sparse Key := [(key1199, -2), (key1019, -2), (key1199, -2), (key1127, 1), (key1199, 1), (key1019, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1193, 2), (key1006, 2), (key1193, 2), (key1041, -1), (key1193, -1), (key1006, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1111, -1), (key1033, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1033, 1)]

def rawRow791 : Integer.Sparse Key := [(key1199, -2), (key1199, -2), (key1019, -2), (key1199, 1), (key1127, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1019, 1), (key1193, 2), (key1193, 2), (key1006, 2), (key1193, -1), (key1041, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1006, -1), (key1190, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1111, -1), (key998, -1), (key1190, 1), (key1033, 1), (key1190, 1), (key998, 1), (key1033, 1), (key998, 1)]

def rawRow792 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 6), (key45, -2), (key45, -2), (key70, -2), (key102, -2), (key102, -2), (key111, -2), (key102, 2), (key102, 2), (key133, 2)]

def rawRow793 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key31, 2), (key20, 2), (key45, 6), (key45, -2), (key70, -2), (key45, -2), (key102, -2), (key111, -2), (key102, -2), (key102, 2), (key133, 2), (key102, 2)]

def rawRow794 : Integer.Sparse Key := [(key20, -6), (key31, 2), (key20, 2), (key20, 2), (key45, 6), (key70, -2), (key45, -2), (key45, -2), (key111, -2), (key102, -2), (key102, -2), (key133, 2), (key102, 2), (key102, 2)]

def rawRow796 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key102, 2), (key111, 2), (key20, 6), (key102, -2), (key102, -2), (key133, -2), (key20, -2), (key20, -2), (key31, -2), (key45, 2), (key45, 2), (key70, 2)]

def rawRow797 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key111, 2), (key102, 2), (key20, 6), (key102, -2), (key133, -2), (key102, -2), (key20, -2), (key31, -2), (key20, -2), (key45, 2), (key70, 2), (key45, 2)]

def rawRow798 : Integer.Sparse Key := [(key45, -6), (key111, 2), (key102, 2), (key102, 2), (key20, 6), (key133, -2), (key102, -2), (key102, -2), (key31, -2), (key20, -2), (key20, -2), (key70, 2), (key45, 2), (key45, 2)]

def rawRow799 : Integer.Sparse Key := [(key111, -6), (key45, 2), (key102, 2), (key102, 2), (key133, 6), (key20, -2), (key102, -2), (key102, -2), (key70, -2), (key133, -2), (key133, -2), (key31, 2), (key111, 2), (key111, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow800 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key45, 2), (key102, 2), (key133, 6), (key102, -2), (key20, -2), (key102, -2), (key133, -2), (key70, -2), (key133, -2), (key111, 2), (key31, 2), (key111, 2)]

def rawRow801 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key102, 2), (key45, 2), (key133, 6), (key102, -2), (key102, -2), (key20, -2), (key133, -2), (key133, -2), (key70, -2), (key111, 2), (key111, 2), (key31, 2)]

def rawRow803 : Integer.Sparse Key := [(key133, -6), (key70, 2), (key133, 2), (key133, 2), (key111, 6), (key31, -2), (key111, -2), (key111, -2), (key45, -2), (key102, -2), (key102, -2), (key20, 2), (key102, 2), (key102, 2)]

def rawRow804 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key70, 2), (key133, 2), (key111, 6), (key111, -2), (key31, -2), (key111, -2), (key102, -2), (key45, -2), (key102, -2), (key102, 2), (key20, 2), (key102, 2)]

def rawRow805 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key133, 2), (key70, 2), (key111, 6), (key111, -2), (key111, -2), (key31, -2), (key102, -2), (key102, -2), (key45, -2), (key102, 2), (key102, 2), (key20, 2)]

def rawRow806 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, 1), (key1001, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1015, 1), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, -1), (key1036, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1071, -1), (key1106, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1123, -1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1)]

def rawRow807 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, 1), (key993, 1), (key1015, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, -1), (key1028, -1), (key1071, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1)]

def rawRow808 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 1), (key1015, 1), (key1001, 1), (key1001, 1), (key993, 1), (key993, 1), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, -1), (key1071, -1), (key1036, -1), (key1036, -1), (key1028, -1), (key1028, -1), (key1123, -1), (key1123, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1)]

def rawRow810 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key993, 2), (key1001, 2), (key1001, 2), (key1106, -1), (key1114, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1150, -1), (key993, -1), (key1001, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1015, -1), (key1028, 1), (key1036, 1), (key1028, 1), (key1071, 1), (key1036, 1), (key1071, 1)]

def rawRow811 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1001, 2), (key993, 2), (key1001, 2), (key1114, -1), (key1106, -1), (key1150, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1001, -1), (key993, -1), (key1015, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1036, 1), (key1028, 1), (key1071, 1), (key1028, 1), (key1071, 1), (key1036, 1)]

def rawRow812 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1001, 2), (key1001, 2), (key993, 2), (key1150, -1), (key1150, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1015, -1), (key1015, -1), (key1001, -1), (key1001, -1), (key993, -1), (key993, -1), (key1071, 1), (key1071, 1), (key1036, 1), (key1036, 1), (key1028, 1), (key1028, 1)]

def rawRow813 : Integer.Sparse Key := [(key1123, -2), (key1123, -2), (key1235, -2), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, -1), (key1001, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1071, -1), (key1071, -1), (key1150, -1), (key1150, -1), (key1242, -1), (key1242, -1), (key1015, 1), (key1015, 1), (key1123, 1), (key1123, 1), (key1235, 1), (key1235, 1)]

def rawRow814 : Integer.Sparse Key := [(key1123, -2), (key1235, -2), (key1123, -2), (key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, -1), (key1232, -1), (key1001, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1123, 1), (key1235, 1), (key1015, 1), (key1235, 1), (key1015, 1), (key1123, 1)]

def rawRow815 : Integer.Sparse Key := [(key1235, -2), (key1123, -2), (key1123, -2), (key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, -1), (key1114, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1001, -1), (key1242, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1071, -1), (key1235, 1), (key1123, 1), (key1235, 1), (key1015, 1), (key1123, 1), (key1015, 1)]

def rawRow817 : Integer.Sparse Key := [(key1150, -2), (key1150, -2), (key1242, -2), (key1071, 1), (key1071, 1), (key1150, 1), (key1150, 1), (key1242, 1), (key1242, 1), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, -1), (key1015, -1), (key1123, -1), (key1123, -1), (key1235, -1), (key1235, -1), (key1036, -1), (key1036, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1)]

def rawRow818 : Integer.Sparse Key := [(key1150, -2), (key1242, -2), (key1150, -2), (key1150, 1), (key1242, 1), (key1071, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, -1), (key1235, -1), (key1015, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1)]

def rawRow819 : Integer.Sparse Key := [(key1242, -2), (key1150, -2), (key1150, -2), (key1242, 1), (key1150, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1071, 1), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, -1), (key1123, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1015, -1), (key1232, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1036, -1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1)]

def rawRow820 : Integer.Sparse Key := [(key1, -2), (key7, -2), (key7, -2), (key7, 6), (key84, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key151, -2), (key193, -6), (key193, 2), (key193, 2), (key202, 2)]

def rawRow821 : Integer.Sparse Key := [(key7, -2), (key1, -2), (key7, -2), (key7, 6), (key90, 2), (key84, 2), (key90, 2), (key90, -2), (key151, -2), (key90, -2), (key193, -6), (key193, 2), (key202, 2), (key193, 2)]

def rawRow822 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key1, -2), (key7, 6), (key90, 2), (key90, 2), (key84, 2), (key151, -2), (key90, -2), (key90, -2), (key193, -6), (key202, 2), (key193, 2), (key193, 2)]

def rawRow824 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key90, -2), (key151, 6), (key1, 2), (key7, 2), (key7, 2), (key193, -2), (key193, -2), (key202, -2), (key7, -6), (key90, 2), (key90, 2), (key151, 2)]

def rawRow825 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key90, -2), (key151, 6), (key7, 2), (key1, 2), (key7, 2), (key193, -2), (key202, -2), (key193, -2), (key7, -6), (key90, 2), (key151, 2), (key90, 2)]

def rawRow826 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key84, -2), (key151, 6), (key7, 2), (key7, 2), (key1, 2), (key202, -2), (key193, -2), (key193, -2), (key7, -6), (key151, 2), (key90, 2), (key90, 2)]

def rawRow827 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key151, -2), (key84, 6), (key193, 2), (key193, 2), (key202, 2), (key1, -2), (key84, -2), (key84, -2), (key151, -6), (key7, 2), (key90, 2), (key90, 2)]

def rawRow828 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key90, -2), (key84, 6), (key193, 2), (key202, 2), (key193, 2), (key84, -2), (key1, -2), (key84, -2), (key151, -6), (key90, 2), (key7, 2), (key90, 2)]

def rawRow829 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key90, -2), (key84, 6), (key202, 2), (key193, 2), (key193, 2), (key84, -2), (key84, -2), (key1, -2), (key151, -6), (key90, 2), (key90, 2), (key7, 2)]

def rawRow831 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key202, -2), (key193, 6), (key90, 2), (key90, 2), (key151, 2), (key7, -2), (key90, -2), (key90, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow832 : Integer.Sparse Key := [(key193, -2), (key202, -2), (key193, -2), (key193, 6), (key90, 2), (key151, 2), (key90, 2), (key90, -2), (key7, -2), (key90, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

def rawRow833 : Integer.Sparse Key := [(key202, -2), (key193, -2), (key193, -2), (key193, 6), (key151, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key7, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

def rawRow835 : Integer.Sparse Key := [(key2670, -2), (key2793, -2), (key2793, -2), (key2670, 1), (key2670, 1), (key2785, 1), (key2785, 1), (key2793, 1), (key2793, 1), (key2705, 2), (key2859, 2), (key2859, 2), (key2705, -1), (key2705, -1), (key2808, -1), (key2808, -1), (key2859, -1), (key2859, -1), (key2725, -1), (key2725, -1), (key2869, -1), (key2869, -1), (key2879, -1), (key2879, -1), (key2725, 1), (key2725, 1), (key2828, 1), (key2828, 1), (key2879, 1), (key2879, 1)]

def rawRow836 : Integer.Sparse Key := [(key2793, -2), (key2670, -2), (key2793, -2), (key2785, 1), (key2793, 1), (key2670, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2859, 2), (key2705, 2), (key2859, 2), (key2808, -1), (key2859, -1), (key2705, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2828, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2828, 1)]

def rawRow837 : Integer.Sparse Key := [(key2793, -2), (key2793, -2), (key2670, -2), (key2793, 1), (key2785, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2670, 1), (key2859, 2), (key2859, 2), (key2705, 2), (key2859, -1), (key2808, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2705, -1), (key2879, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2725, -1), (key2879, 1), (key2828, 1), (key2879, 1), (key2725, 1), (key2828, 1), (key2725, 1)]

def rawRow839 : Integer.Sparse Key := [(key2615, -2), (key2828, -2), (key2828, -2), (key2615, 1), (key2615, 1), (key2808, 1), (key2808, 1), (key2828, 1), (key2828, 1), (key2631, 2), (key2869, 2), (key2869, 2), (key2631, -1), (key2631, -1), (key2785, -1), (key2785, -1), (key2869, -1), (key2869, -1), (key2639, -1), (key2639, -1), (key2859, -1), (key2859, -1), (key2879, -1), (key2879, -1), (key2639, 1), (key2639, 1), (key2793, 1), (key2793, 1), (key2879, 1), (key2879, 1)]

def rawRow840 : Integer.Sparse Key := [(key2828, -2), (key2615, -2), (key2828, -2), (key2808, 1), (key2828, 1), (key2615, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2869, 2), (key2631, 2), (key2869, 2), (key2785, -1), (key2869, -1), (key2631, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2793, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2793, 1)]

def rawRow841 : Integer.Sparse Key := [(key2828, -2), (key2828, -2), (key2615, -2), (key2828, 1), (key2808, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2615, 1), (key2869, 2), (key2869, 2), (key2631, 2), (key2869, -1), (key2785, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2631, -1), (key2879, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2639, -1), (key2879, 1), (key2793, 1), (key2879, 1), (key2639, 1), (key2793, 1), (key2639, 1)]

def rawRow842 : Integer.Sparse Key := [(key2705, -2), (key2859, -2), (key2859, -2), (key2725, 1), (key2725, 1), (key2869, 1), (key2869, 1), (key2879, 1), (key2879, 1), (key2670, 2), (key2793, 2), (key2793, 2), (key2725, -1), (key2725, -1), (key2828, -1), (key2828, -1), (key2879, -1), (key2879, -1), (key2670, -1), (key2670, -1), (key2785, -1), (key2785, -1), (key2793, -1), (key2793, -1), (key2705, 1), (key2705, 1), (key2808, 1), (key2808, 1), (key2859, 1), (key2859, 1)]

def rawRow843 : Integer.Sparse Key := [(key2859, -2), (key2705, -2), (key2859, -2), (key2869, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2793, 2), (key2670, 2), (key2793, 2), (key2828, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2808, 1), (key2859, 1), (key2705, 1), (key2859, 1), (key2705, 1), (key2808, 1)]

def rawRow844 : Integer.Sparse Key := [(key2859, -2), (key2859, -2), (key2705, -2), (key2879, 1), (key2869, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2725, 1), (key2793, 2), (key2793, 2), (key2670, 2), (key2879, -1), (key2828, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2725, -1), (key2793, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2670, -1), (key2859, 1), (key2808, 1), (key2859, 1), (key2705, 1), (key2808, 1), (key2705, 1)]

def rawRow845 : Integer.Sparse Key := [(key2631, -2), (key2869, -2), (key2869, -2), (key2639, 1), (key2639, 1), (key2859, 1), (key2859, 1), (key2879, 1), (key2879, 1), (key2615, 2), (key2828, 2), (key2828, 2), (key2639, -1), (key2639, -1), (key2793, -1), (key2793, -1), (key2879, -1), (key2879, -1), (key2615, -1), (key2615, -1), (key2808, -1), (key2808, -1), (key2828, -1), (key2828, -1), (key2631, 1), (key2631, 1), (key2785, 1), (key2785, 1), (key2869, 1), (key2869, 1)]

def rawRow846 : Integer.Sparse Key := [(key2869, -2), (key2631, -2), (key2869, -2), (key2859, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2828, 2), (key2615, 2), (key2828, 2), (key2793, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2785, 1), (key2869, 1), (key2631, 1), (key2869, 1), (key2631, 1), (key2785, 1)]

def rawRow847 : Integer.Sparse Key := [(key2869, -2), (key2869, -2), (key2631, -2), (key2879, 1), (key2859, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2639, 1), (key2828, 2), (key2828, 2), (key2615, 2), (key2879, -1), (key2793, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2639, -1), (key2828, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2615, -1), (key2869, 1), (key2785, 1), (key2869, 1), (key2631, 1), (key2785, 1), (key2631, 1)]

def rawRow849 : Integer.Sparse Key := [(key1307, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1537, 6), (key1382, -2), (key1537, -2), (key1537, -2), (key1564, -2), (key1613, -2), (key1613, -2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow850 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1537, 6), (key1537, -2), (key1382, -2), (key1537, -2), (key1613, -2), (key1564, -2), (key1613, -2), (key1613, 2), (key1415, 2), (key1613, 2)]

def rawRow851 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1537, 6), (key1537, -2), (key1537, -2), (key1382, -2), (key1613, -2), (key1613, -2), (key1564, -2), (key1613, 2), (key1613, 2), (key1415, 2)]

def rawRow853 : Integer.Sparse Key := [(key1415, -6), (key1382, 2), (key1415, 2), (key1415, 2), (key1564, 6), (key1287, -2), (key1564, -2), (key1564, -2), (key1537, -2), (key1613, -2), (key1613, -2), (key1307, 2), (key1613, 2), (key1613, 2)]

def rawRow854 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 6), (key1564, -2), (key1287, -2), (key1564, -2), (key1613, -2), (key1537, -2), (key1613, -2), (key1613, 2), (key1307, 2), (key1613, 2)]

def rawRow855 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1415, 2), (key1382, 2), (key1564, 6), (key1564, -2), (key1564, -2), (key1287, -2), (key1613, -2), (key1613, -2), (key1537, -2), (key1613, 2), (key1613, 2), (key1307, 2)]

def rawRow856 : Integer.Sparse Key := [(key1537, -6), (key1564, 2), (key1613, 2), (key1613, 2), (key1307, 6), (key1415, -2), (key1613, -2), (key1613, -2), (key1287, -2), (key1307, -2), (key1307, -2), (key1382, 2), (key1537, 2), (key1537, 2)]

def rawRow857 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1564, 2), (key1613, 2), (key1307, 6), (key1613, -2), (key1415, -2), (key1613, -2), (key1307, -2), (key1287, -2), (key1307, -2), (key1537, 2), (key1382, 2), (key1537, 2)]

def rawRow858 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1613, 2), (key1564, 2), (key1307, 6), (key1613, -2), (key1613, -2), (key1415, -2), (key1307, -2), (key1307, -2), (key1287, -2), (key1537, 2), (key1537, 2), (key1382, 2)]

def rawRow859 : Integer.Sparse Key := [(key1564, -6), (key1537, 2), (key1613, 2), (key1613, 2), (key1415, 6), (key1307, -2), (key1613, -2), (key1613, -2), (key1382, -2), (key1415, -2), (key1415, -2), (key1287, 2), (key1564, 2), (key1564, 2)]

def rawRow860 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1537, 2), (key1613, 2), (key1415, 6), (key1613, -2), (key1307, -2), (key1613, -2), (key1415, -2), (key1382, -2), (key1415, -2), (key1564, 2), (key1287, 2), (key1564, 2)]

def rawRow861 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1613, 2), (key1537, 2), (key1415, 6), (key1613, -2), (key1613, -2), (key1307, -2), (key1415, -2), (key1415, -2), (key1382, -2), (key1564, 2), (key1564, 2), (key1287, 2)]

def rawRow863 : Integer.Sparse Key := [(key2626, -2), (key2626, -2), (key2635, -2), (key2610, 1), (key2610, 1), (key2626, 1), (key2626, 1), (key2635, 1), (key2635, 1), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, -1), (key2665, -1), (key2780, -1), (key2780, -1), (key2789, -1), (key2789, -1), (key2803, -1), (key2803, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow864 : Integer.Sparse Key := [(key2626, -2), (key2635, -2), (key2626, -2), (key2626, 1), (key2635, 1), (key2610, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, -1), (key2789, -1), (key2665, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1)]

def rawRow865 : Integer.Sparse Key := [(key2635, -2), (key2626, -2), (key2626, -2), (key2635, 1), (key2626, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2610, 1), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, -1), (key2780, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2665, -1), (key2855, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2803, -1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1)]

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

def rawRow7904 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

def rawRow7905 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

def rawRow7906 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

def rawRow7907 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

def rawRow7908 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

def rawRow7909 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

def rawRow7910 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

def rawRow7911 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

def rawRow7912 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

def rawRow7913 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

def rawRow7914 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

def rawRow7915 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

def rawRow7916 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

def rawRow7917 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

def rawRow7918 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

def rawRow7919 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

def rawRow7920 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7981 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key428, 6), (key456, 6)]

def rawRow7982 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key456, 6), (key428, 6)]

def rawRow7983 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key456, 6), (key428, 6), (key428, 6)]

def rawRow7984 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key428, 6), (key456, 6)]

def rawRow7985 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key456, 6), (key428, 6)]

def rawRow7986 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key208, 6), (key456, 6)]

def rawRow7987 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key456, 6), (key208, 6)]

def rawRow7988 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key208, 6), (key428, 6)]

def rawRow7989 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key428, 6), (key208, 6)]

def rawRow7990 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key208, 6), (key428, 6), (key428, 6)]

def rawRow7991 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key208, 6), (key428, 6)]

def rawRow7992 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key428, 6), (key208, 6)]

def rawRow7993 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key428, 6), (key456, 6)]

def rawRow7994 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key456, 6), (key428, 6)]

def rawRow7995 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key377, 6), (key456, 6)]

def rawRow7996 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key456, 6), (key377, 6)]

def rawRow7997 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key377, 6), (key428, 6)]

def rawRow7998 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key428, 6), (key377, 6)]

def rawRow7999 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key428, 6), (key456, 6)]

def rawRow8000 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key456, 6), (key428, 6)]

def rawRow8001 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key208, 6), (key456, 6)]

def rawRow8002 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key456, 6), (key208, 6)]

def rawRow8003 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key208, 6), (key428, 6)]

def rawRow8004 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key428, 6), (key208, 6)]

def rawRow8005 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key377, 6), (key456, 6)]

def rawRow8006 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key456, 6), (key377, 6)]

def rawRow8007 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key208, 6), (key456, 6)]

def rawRow8008 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key456, 6), (key208, 6)]

def rawRow8009 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key208, 6), (key377, 6)]

def rawRow8010 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key377, 6), (key208, 6)]

def rawRow8011 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key377, 6), (key428, 6)]

def rawRow8012 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key428, 6), (key377, 6)]

def rawRow8013 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key208, 6), (key428, 6)]

def rawRow8014 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key428, 6), (key208, 6)]

def rawRow8015 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key208, 6), (key377, 6)]

def rawRow8016 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key377, 6), (key208, 6)]

def rawRow8017 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key48, -6), (key74, -6), (key206, 2), (key212, 2), (key212, 2), (key426, 2), (key432, 2), (key426, 2), (key460, 2), (key432, 2), (key460, 2), (key659, 2), (key659, 2), (key663, 2)]

def rawRow8018 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key48, -6), (key74, -6), (key212, 2), (key206, 2), (key212, 2), (key432, 2), (key426, 2), (key460, 2), (key426, 2), (key460, 2), (key432, 2), (key659, 2), (key663, 2), (key659, 2)]

def rawRow8019 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key43, -6), (key74, -6), (key212, 2), (key212, 2), (key206, 2), (key460, 2), (key460, 2), (key432, 2), (key432, 2), (key426, 2), (key426, 2), (key663, 2), (key659, 2), (key659, 2)]

def rawRow8020 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key74, -6), (key48, -6), (key426, 2), (key432, 2), (key659, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key212, 2), (key432, 2), (key460, 2)]

def rawRow8021 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key74, -6), (key48, -6), (key432, 2), (key426, 2), (key659, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key212, 2), (key460, 2), (key432, 2)]

def rawRow8022 : Integer.Sparse Key := [(key43, -6), (key74, -6), (key48, -6), (key48, -6), (key426, 2), (key659, 2), (key432, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key432, 2), (key212, 2), (key460, 2)]

def rawRow8023 : Integer.Sparse Key := [(key74, -6), (key43, -6), (key48, -6), (key48, -6), (key659, 2), (key426, 2), (key432, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key432, 2), (key460, 2), (key212, 2)]

def rawRow8024 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key43, -6), (key48, -6), (key432, 2), (key659, 2), (key426, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key460, 2), (key212, 2), (key432, 2)]

def rawRow8025 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key43, -6), (key48, -6), (key659, 2), (key432, 2), (key426, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key460, 2), (key432, 2), (key212, 2)]

def rawRow8026 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key74, -6), (key43, -6), (key460, 2), (key460, 2), (key663, 2), (key212, 2), (key212, 2), (key432, 2), (key432, 2), (key659, 2), (key659, 2), (key206, 2), (key426, 2), (key426, 2)]

def rawRow8027 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key48, -6), (key43, -6), (key460, 2), (key663, 2), (key460, 2), (key432, 2), (key659, 2), (key212, 2), (key659, 2), (key212, 2), (key432, 2), (key426, 2), (key206, 2), (key426, 2)]

def rawRow8028 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key48, -6), (key43, -6), (key663, 2), (key460, 2), (key460, 2), (key659, 2), (key432, 2), (key659, 2), (key212, 2), (key432, 2), (key212, 2), (key426, 2), (key426, 2), (key206, 2)]

def rawRow8029 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key115, -6), (key137, -6), (key18, 2), (key23, 2), (key35, 2), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def rawRow8030 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key115, -6), (key137, -6), (key23, 2), (key18, 2), (key35, 2), (key381, 2), (key375, 2), (key460, 2), (key426, 2), (key490, 2), (key486, 2), (key654, 2), (key663, 2), (key659, 2)]

def rawRow8031 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key105, -6), (key137, -6), (key18, 2), (key35, 2), (key23, 2), (key426, 2), (key486, 2), (key375, 2), (key490, 2), (key381, 2), (key460, 2), (key659, 2), (key654, 2), (key663, 2)]

def rawRow8032 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key105, -6), (key137, -6), (key35, 2), (key18, 2), (key23, 2), (key486, 2), (key426, 2), (key490, 2), (key375, 2), (key460, 2), (key381, 2), (key659, 2), (key663, 2), (key654, 2)]

def rawRow8033 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key100, -6), (key137, -6), (key23, 2), (key35, 2), (key18, 2), (key460, 2), (key490, 2), (key381, 2), (key486, 2), (key375, 2), (key426, 2), (key663, 2), (key654, 2), (key659, 2)]

def rawRow8034 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key100, -6), (key137, -6), (key35, 2), (key23, 2), (key18, 2), (key490, 2), (key460, 2), (key486, 2), (key381, 2), (key426, 2), (key375, 2), (key663, 2), (key659, 2), (key654, 2)]

def rawRow8035 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key137, -6), (key115, -6), (key43, 2), (key48, 2), (key74, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key218, 2), (key486, 2), (key490, 2)]

def rawRow8036 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key137, -6), (key115, -6), (key48, 2), (key43, 2), (key74, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key218, 2), (key490, 2), (key486, 2)]

def rawRow8037 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key105, -6), (key115, -6), (key43, 2), (key74, 2), (key48, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key486, 2), (key218, 2), (key490, 2)]

def rawRow8038 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key105, -6), (key115, -6), (key74, 2), (key43, 2), (key48, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key486, 2), (key490, 2), (key218, 2)]

def rawRow8039 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key100, -6), (key115, -6), (key48, 2), (key74, 2), (key43, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key490, 2), (key218, 2), (key486, 2)]

def rawRow8040 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key100, -6), (key115, -6), (key74, 2), (key48, 2), (key43, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key490, 2), (key486, 2), (key218, 2)]

def rawRow8041 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key137, -6), (key105, -6), (key100, 2), (key115, 2), (key137, 2), (key18, 2), (key35, 2), (key375, 2), (key490, 2), (key654, 2), (key663, 2), (key212, 2), (key381, 2), (key460, 2)]

def rawRow8042 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key137, -6), (key105, -6), (key115, 2), (key100, 2), (key137, 2), (key35, 2), (key18, 2), (key490, 2), (key375, 2), (key663, 2), (key654, 2), (key212, 2), (key460, 2), (key381, 2)]

def rawRow8043 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key115, -6), (key105, -6), (key100, 2), (key137, 2), (key115, 2), (key43, 2), (key74, 2), (key206, 2), (key663, 2), (key218, 2), (key490, 2), (key381, 2), (key212, 2), (key460, 2)]

def rawRow8044 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key115, -6), (key105, -6), (key137, 2), (key100, 2), (key115, 2), (key74, 2), (key43, 2), (key663, 2), (key206, 2), (key490, 2), (key218, 2), (key381, 2), (key460, 2), (key212, 2)]

def rawRow8045 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key100, -6), (key105, -6), (key115, 2), (key137, 2), (key100, 2), (key196, 2), (key200, 2), (key35, 2), (key74, 2), (key18, 2), (key375, 2), (key460, 2), (key212, 2), (key381, 2)]

def rawRow8046 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key100, -6), (key105, -6), (key137, 2), (key115, 2), (key100, 2), (key200, 2), (key196, 2), (key74, 2), (key35, 2), (key43, 2), (key206, 2), (key460, 2), (key381, 2), (key212, 2)]

def rawRow8047 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key137, -6), (key100, -6), (key195, 2), (key196, 2), (key200, 2), (key23, 2), (key35, 2), (key48, 2), (key115, 2), (key74, 2), (key137, 2), (key18, 2), (key375, 2), (key426, 2)]

def rawRow8048 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key137, -6), (key100, -6), (key196, 2), (key195, 2), (key200, 2), (key35, 2), (key23, 2), (key115, 2), (key48, 2), (key137, 2), (key74, 2), (key18, 2), (key426, 2), (key375, 2)]

def rawRow8049 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key115, -6), (key100, -6), (key195, 2), (key200, 2), (key196, 2), (key48, 2), (key74, 2), (key23, 2), (key137, 2), (key35, 2), (key115, 2), (key43, 2), (key206, 2), (key426, 2)]

def rawRow8050 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key115, -6), (key100, -6), (key200, 2), (key195, 2), (key196, 2), (key74, 2), (key48, 2), (key137, 2), (key23, 2), (key115, 2), (key35, 2), (key43, 2), (key426, 2), (key206, 2)]

def rawRow8051 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key105, -6), (key100, -6), (key196, 2), (key200, 2), (key195, 2), (key115, 2), (key137, 2), (key35, 2), (key74, 2), (key23, 2), (key48, 2), (key100, 2), (key18, 2), (key375, 2)]

def rawRow8052 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key105, -6), (key100, -6), (key200, 2), (key196, 2), (key195, 2), (key137, 2), (key115, 2), (key74, 2), (key35, 2), (key48, 2), (key23, 2), (key100, 2), (key43, 2), (key206, 2)]

def rawRow8053 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1570, -6), (key1590, -6), (key1313, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1421, 2), (key1441, 2), (key1619, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1621, 2), (key1630, 2)]

def rawRow8054 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1590, -6), (key1570, -6), (key1313, 2), (key1323, 2), (key1313, 2), (key1421, 2), (key1441, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1619, 2), (key1630, 2), (key1621, 2)]

def rawRow8055 : Integer.Sparse Key := [(key1293, -6), (key1590, -6), (key1570, -6), (key1570, -6), (key1323, 2), (key1313, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1421, 2), (key1630, 2), (key1630, 2), (key1621, 2), (key1621, 2), (key1619, 2), (key1619, 2)]

def rawRow8056 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1570, -6), (key1590, -6), (key1421, 2), (key1619, 2), (key1621, 2), (key1313, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

def rawRow8057 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1590, -6), (key1570, -6), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1619, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

def rawRow8058 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1293, -6), (key1590, -6), (key1619, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

def rawRow8059 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1590, -6), (key1293, -6), (key1619, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

def rawRow8060 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1293, -6), (key1570, -6), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1619, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

def rawRow8061 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1570, -6), (key1293, -6), (key1621, 2), (key1619, 2), (key1421, 2), (key1630, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

def rawRow8062 : Integer.Sparse Key := [(key1590, -6), (key1293, -6), (key1570, -6), (key1570, -6), (key1441, 2), (key1630, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1621, 2), (key1313, 2), (key1313, 2), (key1421, 2), (key1421, 2), (key1619, 2), (key1619, 2)]

def rawRow8063 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1293, -6), (key1570, -6), (key1630, 2), (key1441, 2), (key1630, 2), (key1621, 2), (key1323, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1619, 2), (key1313, 2), (key1421, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8064 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1570, -6), (key1293, -6), (key1630, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1621, 2), (key1323, 2), (key1619, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1421, 2), (key1313, 2)]

def rawRow8065 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1619, -6), (key1630, -6), (key1293, 2), (key1313, 2), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, 2), (key1553, 2), (key1570, 2), (key1590, 2), (key1621, 2), (key1630, 2)]

def rawRow8066 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1630, -6), (key1619, -6), (key1293, 2), (key1323, 2), (key1313, 2), (key1388, 2), (key1441, 2), (key1421, 2), (key1553, 2), (key1543, 2), (key1590, 2), (key1570, 2), (key1630, 2), (key1621, 2)]

def rawRow8067 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1543, -6), (key1630, -6), (key1313, 2), (key1293, 2), (key1323, 2), (key1421, 2), (key1388, 2), (key1441, 2), (key1570, 2), (key1621, 2), (key1543, 2), (key1630, 2), (key1553, 2), (key1590, 2)]

def rawRow8068 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1630, -6), (key1543, -6), (key1313, 2), (key1323, 2), (key1293, 2), (key1421, 2), (key1441, 2), (key1388, 2), (key1621, 2), (key1570, 2), (key1630, 2), (key1543, 2), (key1590, 2), (key1553, 2)]

def rawRow8069 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1543, -6), (key1619, -6), (key1323, 2), (key1293, 2), (key1313, 2), (key1441, 2), (key1388, 2), (key1421, 2), (key1590, 2), (key1630, 2), (key1553, 2), (key1621, 2), (key1543, 2), (key1570, 2)]

def rawRow8070 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1619, -6), (key1543, -6), (key1323, 2), (key1313, 2), (key1293, 2), (key1441, 2), (key1421, 2), (key1388, 2), (key1630, 2), (key1590, 2), (key1621, 2), (key1553, 2), (key1570, 2), (key1543, 2)]

def rawRow8071 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1619, -6), (key1630, -6), (key1388, 2), (key1543, 2), (key1553, 2), (key1293, 2), (key1570, 2), (key1590, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

def rawRow8072 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1630, -6), (key1619, -6), (key1388, 2), (key1553, 2), (key1543, 2), (key1293, 2), (key1590, 2), (key1570, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

def rawRow8073 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1313, -6), (key1630, -6), (key1543, 2), (key1388, 2), (key1553, 2), (key1570, 2), (key1293, 2), (key1590, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

def rawRow8074 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1630, -6), (key1313, -6), (key1543, 2), (key1553, 2), (key1388, 2), (key1570, 2), (key1590, 2), (key1293, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

def rawRow8075 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1313, -6), (key1619, -6), (key1553, 2), (key1388, 2), (key1543, 2), (key1590, 2), (key1293, 2), (key1570, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

def rawRow8076 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1619, -6), (key1313, -6), (key1553, 2), (key1543, 2), (key1388, 2), (key1590, 2), (key1570, 2), (key1293, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

def rawRow8077 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1543, -6), (key1630, -6), (key1421, 2), (key1570, 2), (key1621, 2), (key1313, 2), (key1543, 2), (key1630, 2), (key1293, 2), (key1323, 2), (key1388, 2), (key1441, 2), (key1553, 2), (key1590, 2)]

def rawRow8078 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1630, -6), (key1543, -6), (key1421, 2), (key1621, 2), (key1570, 2), (key1313, 2), (key1630, 2), (key1543, 2), (key1323, 2), (key1293, 2), (key1441, 2), (key1388, 2), (key1590, 2), (key1553, 2)]

def rawRow8079 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1313, -6), (key1630, -6), (key1570, 2), (key1421, 2), (key1621, 2), (key1543, 2), (key1313, 2), (key1630, 2), (key1388, 2), (key1553, 2), (key1293, 2), (key1590, 2), (key1323, 2), (key1441, 2)]

def rawRow8080 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1630, -6), (key1313, -6), (key1570, 2), (key1621, 2), (key1421, 2), (key1543, 2), (key1630, 2), (key1313, 2), (key1553, 2), (key1388, 2), (key1590, 2), (key1293, 2), (key1441, 2), (key1323, 2)]

def rawRow8081 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1313, -6), (key1543, -6), (key1621, 2), (key1421, 2), (key1570, 2), (key1630, 2), (key1313, 2), (key1543, 2), (key1441, 2), (key1590, 2), (key1323, 2), (key1553, 2), (key1293, 2), (key1388, 2)]

def rawRow8082 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1543, -6), (key1313, -6), (key1621, 2), (key1570, 2), (key1421, 2), (key1630, 2), (key1543, 2), (key1313, 2), (key1590, 2), (key1441, 2), (key1553, 2), (key1323, 2), (key1388, 2), (key1293, 2)]

def rawRow8083 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1543, -6), (key1619, -6), (key1441, 2), (key1590, 2), (key1630, 2), (key1323, 2), (key1553, 2), (key1621, 2), (key1293, 2), (key1313, 2), (key1388, 2), (key1421, 2), (key1543, 2), (key1570, 2)]

def rawRow8084 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1619, -6), (key1543, -6), (key1441, 2), (key1630, 2), (key1590, 2), (key1323, 2), (key1621, 2), (key1553, 2), (key1313, 2), (key1293, 2), (key1421, 2), (key1388, 2), (key1570, 2), (key1543, 2)]

def rawRow8085 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1313, -6), (key1619, -6), (key1590, 2), (key1441, 2), (key1630, 2), (key1553, 2), (key1323, 2), (key1621, 2), (key1388, 2), (key1543, 2), (key1293, 2), (key1570, 2), (key1313, 2), (key1421, 2)]

def rawRow8086 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1619, -6), (key1313, -6), (key1590, 2), (key1630, 2), (key1441, 2), (key1553, 2), (key1621, 2), (key1323, 2), (key1543, 2), (key1388, 2), (key1570, 2), (key1293, 2), (key1421, 2), (key1313, 2)]

def rawRow8087 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1313, -6), (key1543, -6), (key1630, 2), (key1441, 2), (key1590, 2), (key1621, 2), (key1323, 2), (key1553, 2), (key1421, 2), (key1570, 2), (key1313, 2), (key1543, 2), (key1293, 2), (key1388, 2)]

def rawRow8088 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1543, -6), (key1313, -6), (key1630, 2), (key1590, 2), (key1441, 2), (key1621, 2), (key1553, 2), (key1323, 2), (key1570, 2), (key1421, 2), (key1543, 2), (key1313, 2), (key1388, 2), (key1293, 2)]

def rawRow8089 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1534, -6), (key1894, -6), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1640, 2), (key1916, 2), (key1916, 2), (key1930, 2)]

def rawRow8090 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1534, -6), (key1894, -6), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1930, 2), (key1916, 2)]

def rawRow8091 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1526, -6), (key1894, -6), (key1259, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1640, 2), (key1612, 2), (key1612, 2), (key1604, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1916, 2)]

def rawRow8092 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1894, -6), (key1534, -6), (key1604, 2), (key1612, 2), (key1916, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1259, 2), (key1612, 2), (key1640, 2)]

def rawRow8093 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1894, -6), (key1534, -6), (key1612, 2), (key1604, 2), (key1916, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1259, 2), (key1640, 2), (key1612, 2)]

def rawRow8094 : Integer.Sparse Key := [(key1526, -6), (key1894, -6), (key1534, -6), (key1534, -6), (key1604, 2), (key1916, 2), (key1612, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1612, 2), (key1259, 2), (key1640, 2)]

def rawRow8095 : Integer.Sparse Key := [(key1894, -6), (key1526, -6), (key1534, -6), (key1534, -6), (key1916, 2), (key1604, 2), (key1612, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1612, 2), (key1640, 2), (key1259, 2)]

def rawRow8096 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1526, -6), (key1534, -6), (key1612, 2), (key1916, 2), (key1604, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1640, 2), (key1259, 2), (key1612, 2)]

def rawRow8097 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1526, -6), (key1534, -6), (key1916, 2), (key1612, 2), (key1604, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1640, 2), (key1612, 2), (key1259, 2)]

def rawRow8098 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1894, -6), (key1526, -6), (key1640, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1259, 2), (key1612, 2), (key1612, 2), (key1916, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1604, 2)]

def rawRow8099 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1534, -6), (key1526, -6), (key1640, 2), (key1930, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1251, 2), (key1604, 2)]

def rawRow8100 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1534, -6), (key1526, -6), (key1930, 2), (key1640, 2), (key1640, 2), (key1916, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1259, 2), (key1604, 2), (key1604, 2), (key1251, 2)]

def rawRow8101 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1679, -6), (key1916, -6), (key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, 2), (key1640, 2), (key1679, 2), (key1693, 2), (key1894, 2), (key1916, 2), (key1930, 2)]

def rawRow8102 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1679, -6), (key1916, -6), (key1259, 2), (key1251, 2), (key1271, 2), (key1534, 2), (key1526, 2), (key1640, 2), (key1604, 2), (key1693, 2), (key1679, 2), (key1894, 2), (key1930, 2), (key1916, 2)]

def rawRow8103 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1612, -6), (key1916, -6), (key1251, 2), (key1271, 2), (key1259, 2), (key1604, 2), (key1679, 2), (key1526, 2), (key1693, 2), (key1534, 2), (key1640, 2), (key1916, 2), (key1894, 2), (key1930, 2)]

def rawRow8104 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1612, -6), (key1916, -6), (key1271, 2), (key1251, 2), (key1259, 2), (key1679, 2), (key1604, 2), (key1693, 2), (key1526, 2), (key1640, 2), (key1534, 2), (key1916, 2), (key1930, 2), (key1894, 2)]

def rawRow8105 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1604, -6), (key1916, -6), (key1259, 2), (key1271, 2), (key1251, 2), (key1640, 2), (key1693, 2), (key1534, 2), (key1679, 2), (key1526, 2), (key1604, 2), (key1930, 2), (key1894, 2), (key1916, 2)]

def rawRow8106 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1604, -6), (key1916, -6), (key1271, 2), (key1259, 2), (key1251, 2), (key1693, 2), (key1640, 2), (key1679, 2), (key1534, 2), (key1604, 2), (key1526, 2), (key1930, 2), (key1916, 2), (key1894, 2)]

def rawRow8107 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1916, -6), (key1679, -6), (key1526, 2), (key1534, 2), (key1894, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1271, 2), (key1679, 2), (key1693, 2)]

def rawRow8108 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1916, -6), (key1679, -6), (key1534, 2), (key1526, 2), (key1894, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1271, 2), (key1693, 2), (key1679, 2)]

def rawRow8109 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1612, -6), (key1679, -6), (key1526, 2), (key1894, 2), (key1534, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1679, 2), (key1271, 2), (key1693, 2)]

def rawRow8110 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1612, -6), (key1679, -6), (key1894, 2), (key1526, 2), (key1534, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1679, 2), (key1693, 2), (key1271, 2)]

def rawRow8111 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1604, -6), (key1679, -6), (key1534, 2), (key1894, 2), (key1526, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1693, 2), (key1271, 2), (key1679, 2)]

def rawRow8112 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1604, -6), (key1679, -6), (key1894, 2), (key1534, 2), (key1526, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1693, 2), (key1679, 2), (key1271, 2)]

def rawRow8113 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1916, -6), (key1612, -6), (key1604, 2), (key1679, 2), (key1916, 2), (key1251, 2), (key1271, 2), (key1526, 2), (key1693, 2), (key1894, 2), (key1930, 2), (key1259, 2), (key1534, 2), (key1640, 2)]

def rawRow8114 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1916, -6), (key1612, -6), (key1679, 2), (key1604, 2), (key1916, 2), (key1271, 2), (key1251, 2), (key1693, 2), (key1526, 2), (key1930, 2), (key1894, 2), (key1259, 2), (key1640, 2), (key1534, 2)]

def rawRow8115 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1679, -6), (key1612, -6), (key1604, 2), (key1916, 2), (key1679, 2), (key1526, 2), (key1894, 2), (key1251, 2), (key1930, 2), (key1271, 2), (key1693, 2), (key1534, 2), (key1259, 2), (key1640, 2)]

def rawRow8116 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1679, -6), (key1612, -6), (key1916, 2), (key1604, 2), (key1679, 2), (key1894, 2), (key1526, 2), (key1930, 2), (key1251, 2), (key1693, 2), (key1271, 2), (key1534, 2), (key1640, 2), (key1259, 2)]

def rawRow8117 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1604, -6), (key1612, -6), (key1679, 2), (key1916, 2), (key1604, 2), (key1693, 2), (key1930, 2), (key1271, 2), (key1894, 2), (key1251, 2), (key1526, 2), (key1640, 2), (key1259, 2), (key1534, 2)]

def rawRow8118 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1604, -6), (key1612, -6), (key1916, 2), (key1679, 2), (key1604, 2), (key1930, 2), (key1693, 2), (key1894, 2), (key1271, 2), (key1526, 2), (key1251, 2), (key1640, 2), (key1534, 2), (key1259, 2)]

def rawRow8119 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1916, -6), (key1604, -6), (key1640, 2), (key1693, 2), (key1930, 2), (key1259, 2), (key1271, 2), (key1534, 2), (key1679, 2), (key1894, 2), (key1916, 2), (key1251, 2), (key1526, 2), (key1604, 2)]

def rawRow8120 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1916, -6), (key1604, -6), (key1693, 2), (key1640, 2), (key1930, 2), (key1271, 2), (key1259, 2), (key1679, 2), (key1534, 2), (key1916, 2), (key1894, 2), (key1251, 2), (key1604, 2), (key1526, 2)]

def rawRow8121 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1679, -6), (key1604, -6), (key1640, 2), (key1930, 2), (key1693, 2), (key1534, 2), (key1894, 2), (key1259, 2), (key1916, 2), (key1271, 2), (key1679, 2), (key1526, 2), (key1251, 2), (key1604, 2)]

def rawRow8122 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1679, -6), (key1604, -6), (key1930, 2), (key1640, 2), (key1693, 2), (key1894, 2), (key1534, 2), (key1916, 2), (key1259, 2), (key1679, 2), (key1271, 2), (key1526, 2), (key1604, 2), (key1251, 2)]

def rawRow8123 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1612, -6), (key1604, -6), (key1693, 2), (key1930, 2), (key1640, 2), (key1679, 2), (key1916, 2), (key1271, 2), (key1894, 2), (key1259, 2), (key1534, 2), (key1604, 2), (key1251, 2), (key1526, 2)]

def rawRow8124 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1612, -6), (key1604, -6), (key1930, 2), (key1693, 2), (key1640, 2), (key1916, 2), (key1679, 2), (key1894, 2), (key1271, 2), (key1534, 2), (key1259, 2), (key1604, 2), (key1526, 2), (key1251, 2)]

def rawRow8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -2), (key1299, -2), (key1568, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1594, -2), (key1904, -2), (key1904, -2), (key1912, -2), (key1311, 1), (key1319, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1327, 1), (key1419, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1445, 1), (key1617, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1634, 1), (key1919, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1921, 1), (key1927, 1)]

def rawRow8126 : Integer.Sparse Key := [(key1299, -2), (key1291, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1912, -2), (key1904, -2), (key1319, 1), (key1311, 1), (key1327, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1919, 1), (key1927, 1), (key1921, 1)]

def rawRow8127 : Integer.Sparse Key := [(key1299, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1594, -2), (key1576, -2), (key1576, -2), (key1568, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1904, -2), (key1327, 1), (key1327, 1), (key1319, 1), (key1319, 1), (key1311, 1), (key1311, 1), (key1445, 1), (key1445, 1), (key1427, 1), (key1427, 1), (key1419, 1), (key1419, 1), (key1634, 1), (key1634, 1), (key1625, 1), (key1625, 1), (key1617, 1), (key1617, 1), (key1927, 1), (key1927, 1), (key1921, 1), (key1921, 1), (key1919, 1), (key1919, 1)]

def rawRow8128 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1291, -2), (key1299, -2), (key1568, -2), (key1594, -2), (key1904, -2), (key1912, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1419, 1), (key1427, 1), (key1617, 1), (key1625, 1), (key1919, 1), (key1921, 1), (key1311, 1), (key1319, 1), (key1617, 1), (key1634, 1), (key1919, 1), (key1927, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1445, 1), (key1625, 1), (key1634, 1)]

def rawRow8129 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1427, 1), (key1419, 1), (key1625, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1319, 1), (key1311, 1), (key1634, 1), (key1617, 1), (key1927, 1), (key1919, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1327, 1), (key1319, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1625, 1)]

def rawRow8130 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1568, -2), (key1904, -2), (key1291, -2), (key1912, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1594, -2), (key1617, 1), (key1919, 1), (key1419, 1), (key1921, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1919, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1445, 1)]

def rawRow8131 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1904, -2), (key1568, -2), (key1912, -2), (key1291, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1299, -2), (key1919, 1), (key1617, 1), (key1921, 1), (key1419, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1634, 1), (key1319, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1445, 1), (key1327, 1)]

def rawRow8132 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1625, 1), (key1921, 1), (key1427, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1634, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1311, 1), (key1617, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1445, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1319, 1), (key1427, 1)]

def rawRow8133 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1912, -2), (key1594, -2), (key1904, -2), (key1299, -2), (key1568, -2), (key1291, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1921, 1), (key1625, 1), (key1919, 1), (key1427, 1), (key1617, 1), (key1419, 1), (key1927, 1), (key1634, 1), (key1919, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1634, 1), (key1445, 1), (key1625, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

def rawRow8134 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1299, -2), (key1576, -2), (key1576, -2), (key1904, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1568, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1), (key1319, 1), (key1319, 1), (key1427, 1), (key1427, 1), (key1919, 1), (key1919, 1), (key1311, 1), (key1311, 1), (key1419, 1), (key1419, 1), (key1617, 1), (key1617, 1)]

def rawRow8135 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1291, -2), (key1568, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1419, 1)]

def rawRow8136 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1904, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1299, -2), (key1568, -2), (key1568, -2), (key1291, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1919, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1319, 1), (key1617, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1419, 1), (key1311, 1)]

def rawRow8137 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1352, -2), (key1541, -2), (key1549, -2), (key1617, -2), (key1634, -2), (key1682, -2), (key1690, -2), (key1897, -2), (key1919, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1327, 1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1921, 1), (key1927, 1)]

def rawRow8138 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1352, -2), (key1549, -2), (key1541, -2), (key1634, -2), (key1617, -2), (key1690, -2), (key1682, -2), (key1897, -2), (key1927, -2), (key1919, -2), (key1299, 1), (key1291, 1), (key1327, 1), (key1311, 1), (key1355, 1), (key1352, 1), (key1394, 1), (key1386, 1), (key1445, 1), (key1419, 1), (key1481, 1), (key1473, 1), (key1557, 1), (key1541, 1), (key1594, 1), (key1568, 1), (key1690, 1), (key1684, 1), (key1900, 1), (key1897, 1), (key1912, 1), (key1904, 1), (key1927, 1), (key1921, 1)]

def rawRow8139 : Integer.Sparse Key := [(key1311, -2), (key1352, -2), (key1319, -2), (key1617, -2), (key1682, -2), (key1541, -2), (key1690, -2), (key1549, -2), (key1634, -2), (key1919, -2), (key1897, -2), (key1927, -2), (key1311, 1), (key1352, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1419, 1), (key1473, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1568, 1), (key1684, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1904, 1), (key1921, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1912, 1)]

def rawRow8140 : Integer.Sparse Key := [(key1352, -2), (key1311, -2), (key1319, -2), (key1682, -2), (key1617, -2), (key1690, -2), (key1541, -2), (key1634, -2), (key1549, -2), (key1919, -2), (key1927, -2), (key1897, -2), (key1352, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1327, 1), (key1299, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1445, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1594, 1), (key1557, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1912, 1), (key1900, 1)]

def rawRow8141 : Integer.Sparse Key := [(key1319, -2), (key1352, -2), (key1311, -2), (key1634, -2), (key1690, -2), (key1549, -2), (key1682, -2), (key1541, -2), (key1617, -2), (key1927, -2), (key1897, -2), (key1919, -2), (key1327, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1291, 1), (key1311, 1), (key1445, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1386, 1), (key1419, 1), (key1594, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1541, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1897, 1), (key1904, 1)]

def rawRow8142 : Integer.Sparse Key := [(key1352, -2), (key1319, -2), (key1311, -2), (key1690, -2), (key1634, -2), (key1682, -2), (key1549, -2), (key1617, -2), (key1541, -2), (key1927, -2), (key1919, -2), (key1897, -2), (key1355, 1), (key1327, 1), (key1352, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1481, 1), (key1445, 1), (key1473, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1690, 1), (key1594, 1), (key1684, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1912, 1), (key1921, 1), (key1900, 1), (key1904, 1), (key1897, 1)]

def rawRow8143 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1634, -2), (key1919, -2), (key1927, -2), (key1352, -2), (key1682, -2), (key1690, -2), (key1386, 1), (key1394, 1), (key1541, 1), (key1557, 1), (key1897, 1), (key1900, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1594, 1), (key1904, 1), (key1912, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1481, 1), (key1684, 1), (key1690, 1)]

def rawRow8144 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1319, -2), (key1311, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1919, -2), (key1352, -2), (key1690, -2), (key1682, -2), (key1394, 1), (key1386, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1897, 1), (key1299, 1), (key1291, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1904, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1355, 1), (key1352, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1684, 1)]

def rawRow8145 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1617, -2), (key1919, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1682, -2), (key1352, -2), (key1690, -2), (key1541, 1), (key1897, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1568, 1), (key1904, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1473, 1), (key1684, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1481, 1)]

def rawRow8146 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1634, -2), (key1319, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1897, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1557, 1), (key1394, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1594, 1), (key1299, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1481, 1), (key1355, 1)]

def rawRow8147 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1634, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1311, -2), (key1617, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1557, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1386, 1), (key1541, 1), (key1594, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1291, 1), (key1568, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1481, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1352, 1), (key1473, 1)]

def rawRow8148 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1927, -2), (key1634, -2), (key1919, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1690, -2), (key1682, -2), (key1352, -2), (key1900, 1), (key1557, 1), (key1897, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1912, 1), (key1594, 1), (key1904, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1690, 1), (key1481, 1), (key1684, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

def rawRow8149 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1311, -2), (key1352, -2), (key1541, -2), (key1690, -2), (key1897, -2), (key1927, -2), (key1319, -2), (key1549, -2), (key1634, -2), (key1419, 1), (key1473, 1), (key1568, 1), (key1684, 1), (key1904, 1), (key1921, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1690, 1), (key1897, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1481, 1), (key1900, 1), (key1912, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1445, 1), (key1557, 1), (key1594, 1)]

def rawRow8150 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1352, -2), (key1311, -2), (key1690, -2), (key1541, -2), (key1927, -2), (key1897, -2), (key1319, -2), (key1634, -2), (key1549, -2), (key1473, 1), (key1419, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1904, 1), (key1352, 1), (key1311, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1897, 1), (key1355, 1), (key1291, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1900, 1), (key1327, 1), (key1299, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1557, 1)]

def rawRow8151 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1541, -2), (key1897, -2), (key1311, -2), (key1927, -2), (key1352, -2), (key1690, -2), (key1549, -2), (key1319, -2), (key1634, -2), (key1568, 1), (key1904, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1541, 1), (key1897, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1386, 1), (key1900, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1394, 1), (key1557, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1445, 1)]

def rawRow8152 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1897, -2), (key1541, -2), (key1927, -2), (key1311, -2), (key1690, -2), (key1352, -2), (key1549, -2), (key1634, -2), (key1319, -2), (key1904, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1684, 1), (key1473, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1690, 1), (key1352, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1481, 1), (key1355, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1445, 1), (key1327, 1)]

def rawRow8153 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1690, -2), (key1927, -2), (key1352, -2), (key1897, -2), (key1311, -2), (key1541, -2), (key1634, -2), (key1319, -2), (key1549, -2), (key1684, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1419, 1), (key1568, 1), (key1690, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1311, 1), (key1541, 1), (key1481, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1291, 1), (key1386, 1), (key1445, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1299, 1), (key1394, 1)]

def rawRow8154 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1927, -2), (key1690, -2), (key1897, -2), (key1352, -2), (key1541, -2), (key1311, -2), (key1634, -2), (key1549, -2), (key1319, -2), (key1921, 1), (key1684, 1), (key1904, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1690, 1), (key1897, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1912, 1), (key1481, 1), (key1900, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1594, 1), (key1445, 1), (key1557, 1), (key1327, 1), (key1394, 1), (key1299, 1)]

def rawRow8155 : Integer.Sparse Key := [(key1634, -2), (key1690, -2), (key1927, -2), (key1319, -2), (key1352, -2), (key1549, -2), (key1682, -2), (key1897, -2), (key1919, -2), (key1311, -2), (key1541, -2), (key1617, -2), (key1445, 1), (key1481, 1), (key1594, 1), (key1690, 1), (key1912, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1684, 1), (key1900, 1), (key1921, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1473, 1), (key1897, 1), (key1904, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1419, 1), (key1541, 1), (key1568, 1)]

def rawRow8156 : Integer.Sparse Key := [(key1690, -2), (key1634, -2), (key1927, -2), (key1352, -2), (key1319, -2), (key1682, -2), (key1549, -2), (key1919, -2), (key1897, -2), (key1311, -2), (key1617, -2), (key1541, -2), (key1481, 1), (key1445, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1327, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1900, 1), (key1352, 1), (key1299, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1897, 1), (key1311, 1), (key1291, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1541, 1)]

def rawRow8157 : Integer.Sparse Key := [(key1634, -2), (key1927, -2), (key1690, -2), (key1549, -2), (key1897, -2), (key1319, -2), (key1919, -2), (key1352, -2), (key1682, -2), (key1541, -2), (key1311, -2), (key1617, -2), (key1594, 1), (key1912, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1557, 1), (key1900, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1897, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1386, 1), (key1541, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1419, 1)]

def rawRow8158 : Integer.Sparse Key := [(key1927, -2), (key1634, -2), (key1690, -2), (key1897, -2), (key1549, -2), (key1919, -2), (key1319, -2), (key1682, -2), (key1352, -2), (key1541, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1690, 1), (key1481, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1684, 1), (key1355, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1473, 1), (key1352, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1419, 1), (key1311, 1)]

def rawRow8159 : Integer.Sparse Key := [(key1690, -2), (key1927, -2), (key1634, -2), (key1682, -2), (key1919, -2), (key1352, -2), (key1897, -2), (key1319, -2), (key1549, -2), (key1617, -2), (key1311, -2), (key1541, -2), (key1690, 1), (key1927, 1), (key1481, 1), (key1912, 1), (key1445, 1), (key1594, 1), (key1684, 1), (key1921, 1), (key1355, 1), (key1900, 1), (key1327, 1), (key1557, 1), (key1473, 1), (key1904, 1), (key1352, 1), (key1897, 1), (key1299, 1), (key1394, 1), (key1419, 1), (key1568, 1), (key1311, 1), (key1541, 1), (key1291, 1), (key1386, 1)]

def rawRow8160 : Integer.Sparse Key := [(key1927, -2), (key1690, -2), (key1634, -2), (key1919, -2), (key1682, -2), (key1897, -2), (key1352, -2), (key1549, -2), (key1319, -2), (key1617, -2), (key1541, -2), (key1311, -2), (key1927, 1), (key1690, 1), (key1912, 1), (key1481, 1), (key1594, 1), (key1445, 1), (key1921, 1), (key1684, 1), (key1900, 1), (key1355, 1), (key1557, 1), (key1327, 1), (key1904, 1), (key1473, 1), (key1897, 1), (key1352, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1419, 1), (key1541, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow8161 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1606, 6), (key1636, 6)]

def rawRow8162 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1606, 6)]

def rawRow8163 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1606, 6)]

def rawRow8164 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

def rawRow8165 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

def rawRow8166 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

def rawRow8167 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

def rawRow8168 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

def rawRow8169 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

def rawRow8170 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1606, 6)]

def rawRow8171 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1606, 6)]

def rawRow8172 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1606, 6), (key1253, 6)]

def rawRow8173 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1606, 6), (key1636, 6)]

def rawRow8174 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1636, 6), (key1606, 6)]

def rawRow8175 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1528, 6), (key1636, 6)]

def rawRow8176 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1528, 6)]

def rawRow8177 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1528, 6), (key1606, 6)]

def rawRow8178 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1528, 6)]

def rawRow8179 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

def rawRow8180 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

def rawRow8181 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

def rawRow8182 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

def rawRow8183 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

def rawRow8184 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

def rawRow8185 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1528, 6), (key1636, 6)]

def rawRow8186 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1528, 6)]

def rawRow8187 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1253, 6), (key1636, 6)]

def rawRow8188 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1636, 6), (key1253, 6)]

def rawRow8189 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1528, 6)]

def rawRow8190 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1528, 6), (key1253, 6)]

def rawRow8191 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1528, 6), (key1606, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8192 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1528, 6)]

def rawRow8193 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1253, 6), (key1606, 6)]

def rawRow8194 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1606, 6), (key1253, 6)]

def rawRow8195 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1528, 6)]

def rawRow8196 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1528, 6), (key1253, 6)]

def rawRow8209 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1473, -2), (key1568, -2), (key1576, -2), (key1617, -2), (key1625, -2), (key1682, -2), (key1684, -2), (key1904, -2), (key1919, -2), (key1921, -2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2)]

def rawRow8210 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1473, -2), (key1576, -2), (key1568, -2), (key1625, -2), (key1617, -2), (key1684, -2), (key1682, -2), (key1904, -2), (key1921, -2), (key1919, -2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2)]

def rawRow8211 : Integer.Sparse Key := [(key1419, -2), (key1473, -2), (key1427, -2), (key1617, -2), (key1682, -2), (key1568, -2), (key1684, -2), (key1576, -2), (key1625, -2), (key1919, -2), (key1904, -2), (key1921, -2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2)]

def rawRow8212 : Integer.Sparse Key := [(key1473, -2), (key1419, -2), (key1427, -2), (key1682, -2), (key1617, -2), (key1684, -2), (key1568, -2), (key1625, -2), (key1576, -2), (key1919, -2), (key1921, -2), (key1904, -2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2)]

def rawRow8213 : Integer.Sparse Key := [(key1427, -2), (key1473, -2), (key1419, -2), (key1625, -2), (key1684, -2), (key1576, -2), (key1682, -2), (key1568, -2), (key1617, -2), (key1921, -2), (key1904, -2), (key1919, -2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2)]

def rawRow8214 : Integer.Sparse Key := [(key1473, -2), (key1427, -2), (key1419, -2), (key1684, -2), (key1625, -2), (key1682, -2), (key1576, -2), (key1617, -2), (key1568, -2), (key1921, -2), (key1919, -2), (key1904, -2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2)]

def rawRow8215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1625, -2), (key1919, -2), (key1921, -2), (key1473, -2), (key1682, -2), (key1684, -2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2)]

def rawRow8216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1427, -2), (key1419, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1919, -2), (key1473, -2), (key1684, -2), (key1682, -2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2)]

def rawRow8217 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1617, -2), (key1919, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1682, -2), (key1473, -2), (key1684, -2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2)]

def rawRow8218 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1625, -2), (key1427, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2)]

def rawRow8219 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1625, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1419, -2), (key1617, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2)]

def rawRow8220 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1921, -2), (key1625, -2), (key1919, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1684, -2), (key1682, -2), (key1473, -2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2)]

def rawRow8221 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1419, -2), (key1473, -2), (key1568, -2), (key1684, -2), (key1904, -2), (key1921, -2), (key1427, -2), (key1576, -2), (key1625, -2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2)]

def rawRow8222 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1473, -2), (key1419, -2), (key1684, -2), (key1568, -2), (key1921, -2), (key1904, -2), (key1427, -2), (key1625, -2), (key1576, -2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2)]

def rawRow8223 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1568, -2), (key1904, -2), (key1419, -2), (key1921, -2), (key1473, -2), (key1684, -2), (key1576, -2), (key1427, -2), (key1625, -2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2)]

def rawRow8224 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1904, -2), (key1568, -2), (key1921, -2), (key1419, -2), (key1684, -2), (key1473, -2), (key1576, -2), (key1625, -2), (key1427, -2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2)]

def rawRow8225 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1684, -2), (key1921, -2), (key1473, -2), (key1904, -2), (key1419, -2), (key1568, -2), (key1625, -2), (key1427, -2), (key1576, -2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2)]

def rawRow8226 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1921, -2), (key1684, -2), (key1904, -2), (key1473, -2), (key1568, -2), (key1419, -2), (key1625, -2), (key1576, -2), (key1427, -2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2)]

def rawRow8227 : Integer.Sparse Key := [(key1625, -2), (key1684, -2), (key1921, -2), (key1427, -2), (key1473, -2), (key1576, -2), (key1682, -2), (key1904, -2), (key1919, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2)]

def rawRow8228 : Integer.Sparse Key := [(key1684, -2), (key1625, -2), (key1921, -2), (key1473, -2), (key1427, -2), (key1682, -2), (key1576, -2), (key1919, -2), (key1904, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2)]

def rawRow8229 : Integer.Sparse Key := [(key1625, -2), (key1921, -2), (key1684, -2), (key1576, -2), (key1904, -2), (key1427, -2), (key1919, -2), (key1473, -2), (key1682, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2)]

def rawRow8230 : Integer.Sparse Key := [(key1921, -2), (key1625, -2), (key1684, -2), (key1904, -2), (key1576, -2), (key1919, -2), (key1427, -2), (key1682, -2), (key1473, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2)]

def rawRow8231 : Integer.Sparse Key := [(key1684, -2), (key1921, -2), (key1625, -2), (key1682, -2), (key1919, -2), (key1473, -2), (key1904, -2), (key1427, -2), (key1576, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2)]

def rawRow8232 : Integer.Sparse Key := [(key1921, -2), (key1684, -2), (key1625, -2), (key1919, -2), (key1682, -2), (key1904, -2), (key1473, -2), (key1576, -2), (key1427, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2)]

def rawRow8233 : Integer.Sparse Key := [(key236, -2), (key241, -2), (key241, -2), (key406, -2), (key411, -2), (key406, -2), (key421, -2), (key411, -2), (key421, -2), (key657, -2), (key657, -2), (key658, -2), (key248, 1), (key253, 1), (key248, 1), (key263, 1), (key253, 1), (key263, 1), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1), (key435, 1), (key445, 1), (key435, 1), (key453, 1), (key445, 1), (key453, 1), (key660, 1), (key661, 1), (key660, 1), (key662, 1), (key661, 1), (key662, 1)]

def rawRow8234 : Integer.Sparse Key := [(key241, -2), (key236, -2), (key241, -2), (key411, -2), (key406, -2), (key421, -2), (key406, -2), (key421, -2), (key411, -2), (key657, -2), (key658, -2), (key657, -2), (key253, 1), (key248, 1), (key263, 1), (key248, 1), (key263, 1), (key253, 1), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1), (key445, 1), (key435, 1), (key453, 1), (key435, 1), (key453, 1), (key445, 1), (key661, 1), (key660, 1), (key662, 1), (key660, 1), (key662, 1), (key661, 1)]

def rawRow8235 : Integer.Sparse Key := [(key241, -2), (key241, -2), (key236, -2), (key421, -2), (key421, -2), (key411, -2), (key411, -2), (key406, -2), (key406, -2), (key658, -2), (key657, -2), (key657, -2), (key263, 1), (key263, 1), (key253, 1), (key253, 1), (key248, 1), (key248, 1), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key453, 1), (key453, 1), (key445, 1), (key445, 1), (key435, 1), (key435, 1), (key662, 1), (key662, 1), (key661, 1), (key661, 1), (key660, 1), (key660, 1)]

def rawRow8236 : Integer.Sparse Key := [(key406, -2), (key411, -2), (key421, -2), (key236, -2), (key241, -2), (key406, -2), (key421, -2), (key657, -2), (key658, -2), (key241, -2), (key411, -2), (key421, -2), (key316, 1), (key321, 1), (key435, 1), (key445, 1), (key660, 1), (key661, 1), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key253, 1), (key263, 1), (key321, 1), (key331, 1), (key445, 1), (key453, 1)]

def rawRow8237 : Integer.Sparse Key := [(key411, -2), (key406, -2), (key421, -2), (key241, -2), (key236, -2), (key421, -2), (key406, -2), (key658, -2), (key657, -2), (key241, -2), (key421, -2), (key411, -2), (key321, 1), (key316, 1), (key445, 1), (key435, 1), (key661, 1), (key660, 1), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key263, 1), (key253, 1), (key331, 1), (key321, 1), (key453, 1), (key445, 1)]

def rawRow8238 : Integer.Sparse Key := [(key406, -2), (key421, -2), (key411, -2), (key406, -2), (key421, -2), (key236, -2), (key658, -2), (key241, -2), (key421, -2), (key411, -2), (key241, -2), (key421, -2), (key435, 1), (key660, 1), (key316, 1), (key661, 1), (key321, 1), (key445, 1), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key321, 1), (key445, 1), (key253, 1), (key453, 1), (key263, 1), (key331, 1)]

def rawRow8239 : Integer.Sparse Key := [(key421, -2), (key406, -2), (key411, -2), (key421, -2), (key406, -2), (key658, -2), (key236, -2), (key421, -2), (key241, -2), (key411, -2), (key421, -2), (key241, -2), (key660, 1), (key435, 1), (key661, 1), (key316, 1), (key445, 1), (key321, 1), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key445, 1), (key321, 1), (key453, 1), (key253, 1), (key331, 1), (key263, 1)]

def rawRow8240 : Integer.Sparse Key := [(key411, -2), (key421, -2), (key406, -2), (key657, -2), (key658, -2), (key241, -2), (key421, -2), (key236, -2), (key406, -2), (key421, -2), (key241, -2), (key411, -2), (key445, 1), (key661, 1), (key321, 1), (key660, 1), (key316, 1), (key435, 1), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key331, 1), (key453, 1), (key263, 1), (key445, 1), (key253, 1), (key321, 1)]

def rawRow8241 : Integer.Sparse Key := [(key421, -2), (key411, -2), (key406, -2), (key658, -2), (key657, -2), (key421, -2), (key241, -2), (key406, -2), (key236, -2), (key421, -2), (key411, -2), (key241, -2), (key661, 1), (key445, 1), (key660, 1), (key321, 1), (key435, 1), (key316, 1), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key453, 1), (key331, 1), (key445, 1), (key263, 1), (key321, 1), (key253, 1)]

def rawRow8242 : Integer.Sparse Key := [(key657, -2), (key657, -2), (key658, -2), (key241, -2), (key241, -2), (key411, -2), (key411, -2), (key421, -2), (key421, -2), (key236, -2), (key406, -2), (key406, -2), (key331, 1), (key331, 1), (key453, 1), (key453, 1), (key662, 1), (key662, 1), (key263, 1), (key263, 1), (key445, 1), (key445, 1), (key661, 1), (key661, 1), (key253, 1), (key253, 1), (key321, 1), (key321, 1), (key660, 1), (key660, 1), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

def rawRow8243 : Integer.Sparse Key := [(key657, -2), (key658, -2), (key657, -2), (key411, -2), (key421, -2), (key241, -2), (key421, -2), (key241, -2), (key411, -2), (key406, -2), (key236, -2), (key406, -2), (key453, 1), (key662, 1), (key331, 1), (key662, 1), (key331, 1), (key453, 1), (key445, 1), (key661, 1), (key263, 1), (key661, 1), (key263, 1), (key445, 1), (key321, 1), (key660, 1), (key253, 1), (key660, 1), (key253, 1), (key321, 1), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

def rawRow8244 : Integer.Sparse Key := [(key658, -2), (key657, -2), (key657, -2), (key421, -2), (key411, -2), (key421, -2), (key241, -2), (key411, -2), (key241, -2), (key406, -2), (key406, -2), (key236, -2), (key662, 1), (key453, 1), (key662, 1), (key331, 1), (key453, 1), (key331, 1), (key661, 1), (key445, 1), (key661, 1), (key263, 1), (key445, 1), (key263, 1), (key660, 1), (key321, 1), (key660, 1), (key253, 1), (key321, 1), (key253, 1), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

def rawRow8245 : Integer.Sparse Key := [(key248, -2), (key253, -2), (key263, -2), (key316, -2), (key321, -2), (key435, -2), (key660, -2), (key445, -2), (key661, -2), (key331, -2), (key453, -2), (key662, -2), (key236, 1), (key241, 1), (key248, 1), (key263, 1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key661, 1), (key662, 1)]

def rawRow8246 : Integer.Sparse Key := [(key253, -2), (key248, -2), (key263, -2), (key321, -2), (key316, -2), (key660, -2), (key435, -2), (key661, -2), (key445, -2), (key331, -2), (key662, -2), (key453, -2), (key241, 1), (key236, 1), (key263, 1), (key248, 1), (key278, 1), (key277, 1), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1), (key400, 1), (key385, 1), (key421, 1), (key406, 1), (key489, 1), (key488, 1), (key656, 1), (key655, 1), (key658, 1), (key657, 1), (key662, 1), (key661, 1)]

def rawRow8247 : Integer.Sparse Key := [(key248, -2), (key263, -2), (key253, -2), (key435, -2), (key445, -2), (key316, -2), (key661, -2), (key321, -2), (key660, -2), (key453, -2), (key331, -2), (key662, -2), (key248, 1), (key263, 1), (key236, 1), (key278, 1), (key241, 1), (key263, 1), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1), (key406, 1), (key488, 1), (key385, 1), (key489, 1), (key400, 1), (key421, 1), (key657, 1), (key661, 1), (key655, 1), (key662, 1), (key656, 1), (key658, 1)]

def rawRow8248 : Integer.Sparse Key := [(key263, -2), (key248, -2), (key253, -2), (key445, -2), (key435, -2), (key661, -2), (key316, -2), (key660, -2), (key321, -2), (key453, -2), (key662, -2), (key331, -2), (key263, 1), (key248, 1), (key278, 1), (key236, 1), (key263, 1), (key241, 1), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key488, 1), (key406, 1), (key489, 1), (key385, 1), (key421, 1), (key400, 1), (key661, 1), (key657, 1), (key662, 1), (key655, 1), (key658, 1), (key656, 1)]

def rawRow8249 : Integer.Sparse Key := [(key253, -2), (key263, -2), (key248, -2), (key660, -2), (key661, -2), (key321, -2), (key445, -2), (key316, -2), (key435, -2), (key662, -2), (key331, -2), (key453, -2), (key277, 1), (key278, 1), (key241, 1), (key263, 1), (key236, 1), (key248, 1), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key421, 1), (key489, 1), (key400, 1), (key488, 1), (key385, 1), (key406, 1), (key658, 1), (key662, 1), (key656, 1), (key661, 1), (key655, 1), (key657, 1)]

def rawRow8250 : Integer.Sparse Key := [(key263, -2), (key253, -2), (key248, -2), (key661, -2), (key660, -2), (key445, -2), (key321, -2), (key435, -2), (key316, -2), (key662, -2), (key453, -2), (key331, -2), (key278, 1), (key277, 1), (key263, 1), (key241, 1), (key248, 1), (key236, 1), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key489, 1), (key421, 1), (key488, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key658, 1), (key661, 1), (key656, 1), (key657, 1), (key655, 1)]

def rawRow8251 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key248, -2), (key253, -2), (key435, -2), (key660, -2), (key453, -2), (key662, -2), (key263, -2), (key445, -2), (key661, -2), (key302, 1), (key307, 1), (key316, 1), (key346, 1), (key331, 1), (key347, 1), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key347, 1), (key488, 1), (key489, 1)]

def rawRow8252 : Integer.Sparse Key := [(key321, -2), (key316, -2), (key331, -2), (key253, -2), (key248, -2), (key660, -2), (key435, -2), (key662, -2), (key453, -2), (key263, -2), (key661, -2), (key445, -2), (key307, 1), (key302, 1), (key346, 1), (key316, 1), (key347, 1), (key331, 1), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key278, 1), (key277, 1), (key347, 1), (key346, 1), (key489, 1), (key488, 1)]

def rawRow8253 : Integer.Sparse Key := [(key316, -2), (key331, -2), (key321, -2), (key435, -2), (key453, -2), (key248, -2), (key662, -2), (key253, -2), (key660, -2), (key445, -2), (key263, -2), (key661, -2), (key316, 1), (key331, 1), (key302, 1), (key347, 1), (key307, 1), (key346, 1), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key346, 1), (key488, 1), (key277, 1), (key489, 1), (key278, 1), (key347, 1)]

def rawRow8254 : Integer.Sparse Key := [(key331, -2), (key316, -2), (key321, -2), (key453, -2), (key435, -2), (key662, -2), (key248, -2), (key660, -2), (key253, -2), (key445, -2), (key661, -2), (key263, -2), (key331, 1), (key316, 1), (key347, 1), (key302, 1), (key346, 1), (key307, 1), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key488, 1), (key346, 1), (key489, 1), (key277, 1), (key347, 1), (key278, 1)]

def rawRow8255 : Integer.Sparse Key := [(key321, -2), (key331, -2), (key316, -2), (key660, -2), (key662, -2), (key253, -2), (key453, -2), (key248, -2), (key435, -2), (key661, -2), (key263, -2), (key445, -2), (key346, 1), (key347, 1), (key307, 1), (key331, 1), (key302, 1), (key316, 1), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key347, 1), (key489, 1), (key278, 1), (key488, 1), (key277, 1), (key346, 1)]

def rawRow8256 : Integer.Sparse Key := [(key331, -2), (key321, -2), (key316, -2), (key662, -2), (key660, -2), (key453, -2), (key253, -2), (key435, -2), (key248, -2), (key661, -2), (key445, -2), (key263, -2), (key347, 1), (key346, 1), (key331, 1), (key307, 1), (key316, 1), (key302, 1), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key489, 1), (key347, 1), (key488, 1), (key278, 1), (key346, 1), (key277, 1)]

def rawRow8257 : Integer.Sparse Key := [(key435, -2), (key445, -2), (key453, -2), (key248, -2), (key263, -2), (key316, -2), (key661, -2), (key331, -2), (key662, -2), (key253, -2), (key321, -2), (key660, -2), (key385, 1), (key400, 1), (key406, 1), (key488, 1), (key421, 1), (key489, 1), (key248, 1), (key263, 1), (key316, 1), (key661, 1), (key331, 1), (key662, 1), (key236, 1), (key278, 1), (key302, 1), (key347, 1), (key656, 1), (key658, 1), (key241, 1), (key263, 1), (key307, 1), (key331, 1), (key400, 1), (key421, 1)]

def rawRow8258 : Integer.Sparse Key := [(key445, -2), (key435, -2), (key453, -2), (key263, -2), (key248, -2), (key661, -2), (key316, -2), (key662, -2), (key331, -2), (key253, -2), (key660, -2), (key321, -2), (key400, 1), (key385, 1), (key488, 1), (key406, 1), (key489, 1), (key421, 1), (key263, 1), (key248, 1), (key661, 1), (key316, 1), (key662, 1), (key331, 1), (key278, 1), (key236, 1), (key347, 1), (key302, 1), (key658, 1), (key656, 1), (key263, 1), (key241, 1), (key331, 1), (key307, 1), (key421, 1), (key400, 1)]

def rawRow8259 : Integer.Sparse Key := [(key435, -2), (key453, -2), (key445, -2), (key316, -2), (key331, -2), (key248, -2), (key662, -2), (key263, -2), (key661, -2), (key321, -2), (key253, -2), (key660, -2), (key406, 1), (key421, 1), (key385, 1), (key489, 1), (key400, 1), (key488, 1), (key316, 1), (key331, 1), (key248, 1), (key662, 1), (key263, 1), (key661, 1), (key302, 1), (key347, 1), (key236, 1), (key658, 1), (key278, 1), (key347, 1), (key307, 1), (key400, 1), (key241, 1), (key421, 1), (key263, 1), (key331, 1)]

def rawRow8260 : Integer.Sparse Key := [(key453, -2), (key435, -2), (key445, -2), (key331, -2), (key316, -2), (key662, -2), (key248, -2), (key661, -2), (key263, -2), (key321, -2), (key660, -2), (key253, -2), (key421, 1), (key406, 1), (key489, 1), (key385, 1), (key488, 1), (key400, 1), (key331, 1), (key316, 1), (key662, 1), (key248, 1), (key661, 1), (key263, 1), (key347, 1), (key302, 1), (key658, 1), (key236, 1), (key347, 1), (key278, 1), (key400, 1), (key307, 1), (key421, 1), (key241, 1), (key331, 1), (key263, 1)]

def rawRow8261 : Integer.Sparse Key := [(key445, -2), (key453, -2), (key435, -2), (key661, -2), (key662, -2), (key263, -2), (key331, -2), (key248, -2), (key316, -2), (key660, -2), (key253, -2), (key321, -2), (key488, 1), (key489, 1), (key400, 1), (key421, 1), (key385, 1), (key406, 1), (key661, 1), (key662, 1), (key263, 1), (key331, 1), (key248, 1), (key316, 1), (key656, 1), (key658, 1), (key278, 1), (key347, 1), (key236, 1), (key302, 1), (key331, 1), (key421, 1), (key263, 1), (key400, 1), (key241, 1), (key307, 1)]

def rawRow8262 : Integer.Sparse Key := [(key453, -2), (key445, -2), (key435, -2), (key662, -2), (key661, -2), (key331, -2), (key263, -2), (key316, -2), (key248, -2), (key660, -2), (key321, -2), (key253, -2), (key489, 1), (key488, 1), (key421, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key661, 1), (key331, 1), (key263, 1), (key316, 1), (key248, 1), (key658, 1), (key656, 1), (key347, 1), (key278, 1), (key302, 1), (key236, 1), (key421, 1), (key331, 1), (key400, 1), (key263, 1), (key307, 1), (key241, 1)]

def rawRow8263 : Integer.Sparse Key := [(key660, -2), (key661, -2), (key662, -2), (key253, -2), (key263, -2), (key321, -2), (key445, -2), (key331, -2), (key453, -2), (key248, -2), (key316, -2), (key435, -2), (key655, 1), (key656, 1), (key657, 1), (key661, 1), (key658, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key488, 1), (key347, 1), (key489, 1), (key241, 1), (key263, 1), (key307, 1), (key400, 1), (key331, 1), (key421, 1), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

def rawRow8264 : Integer.Sparse Key := [(key661, -2), (key660, -2), (key662, -2), (key263, -2), (key253, -2), (key445, -2), (key321, -2), (key453, -2), (key331, -2), (key248, -2), (key435, -2), (key316, -2), (key656, 1), (key655, 1), (key661, 1), (key657, 1), (key662, 1), (key658, 1), (key278, 1), (key277, 1), (key488, 1), (key346, 1), (key489, 1), (key347, 1), (key263, 1), (key241, 1), (key400, 1), (key307, 1), (key421, 1), (key331, 1), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

def rawRow8265 : Integer.Sparse Key := [(key660, -2), (key662, -2), (key661, -2), (key321, -2), (key331, -2), (key253, -2), (key453, -2), (key263, -2), (key445, -2), (key316, -2), (key248, -2), (key435, -2), (key657, 1), (key658, 1), (key655, 1), (key662, 1), (key656, 1), (key661, 1), (key346, 1), (key347, 1), (key277, 1), (key489, 1), (key278, 1), (key488, 1), (key307, 1), (key331, 1), (key241, 1), (key421, 1), (key263, 1), (key400, 1), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

def rawRow8266 : Integer.Sparse Key := [(key662, -2), (key660, -2), (key661, -2), (key331, -2), (key321, -2), (key453, -2), (key253, -2), (key445, -2), (key263, -2), (key316, -2), (key435, -2), (key248, -2), (key658, 1), (key657, 1), (key662, 1), (key655, 1), (key661, 1), (key656, 1), (key347, 1), (key346, 1), (key489, 1), (key277, 1), (key488, 1), (key278, 1), (key331, 1), (key307, 1), (key421, 1), (key241, 1), (key400, 1), (key263, 1), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

def rawRow8267 : Integer.Sparse Key := [(key661, -2), (key662, -2), (key660, -2), (key445, -2), (key453, -2), (key263, -2), (key331, -2), (key253, -2), (key321, -2), (key435, -2), (key248, -2), (key316, -2), (key661, 1), (key662, 1), (key656, 1), (key658, 1), (key655, 1), (key657, 1), (key488, 1), (key489, 1), (key278, 1), (key347, 1), (key277, 1), (key346, 1), (key400, 1), (key421, 1), (key263, 1), (key331, 1), (key241, 1), (key307, 1), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

def rawRow8268 : Integer.Sparse Key := [(key662, -2), (key661, -2), (key660, -2), (key453, -2), (key445, -2), (key331, -2), (key263, -2), (key321, -2), (key253, -2), (key435, -2), (key316, -2), (key248, -2), (key662, 1), (key661, 1), (key658, 1), (key656, 1), (key657, 1), (key655, 1), (key489, 1), (key488, 1), (key347, 1), (key278, 1), (key346, 1), (key277, 1), (key421, 1), (key400, 1), (key331, 1), (key263, 1), (key307, 1), (key241, 1), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

def rawRow8281 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

def rawRow8282 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

def rawRow8283 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

def rawRow8284 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1104, 6)]

def rawRow8285 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1104, 6)]

def rawRow8286 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key991, 6)]

def rawRow8287 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1104, 6)]

def rawRow8288 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1026, 6)]

def rawRow8289 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1104, 6)]

def rawRow8290 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key991, 6)]

def rawRow8291 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1026, 6)]

def rawRow8292 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key991, 6)]

def rawRow8293 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1235, -6), (key1242, -6), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1150, 2)]

def rawRow8294 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1232, -6), (key1242, -6), (key1001, 2), (key1015, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1071, 2), (key1150, 2)]

def rawRow8295 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1232, -6), (key1242, -6), (key1015, 2), (key1001, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1071, 2)]

def rawRow8296 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1242, -6), (key1235, -6), (key1036, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2)]

def rawRow8297 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1232, -6), (key1235, -6), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1015, 2), (key1123, 2)]

def rawRow8298 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1232, -6), (key1235, -6), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1123, 2), (key1123, 2), (key1015, 2)]

def rawRow8299 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1242, -6), (key1232, -6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1001, 2), (key1036, 2), (key1114, 2)]

def rawRow8300 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1242, -6), (key1232, -6), (key1123, 2), (key1114, 2), (key1150, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key1001, 2), (key1114, 2), (key1036, 2)]

def rawRow8301 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1235, -6), (key1232, -6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1001, 2), (key1114, 2)]

def rawRow8302 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1235, -6), (key1232, -6), (key1150, 2), (key1114, 2), (key1123, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1114, 2), (key1001, 2)]

def rawRow8303 : Integer.Sparse Key := [(key1235, -6), (key1242, -6), (key1232, -6), (key1232, -6), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow8304 : Integer.Sparse Key := [(key1242, -6), (key1235, -6), (key1232, -6), (key1232, -6), (key1150, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1001, 2)]

def rawRow8305 : Integer.Sparse Key := [(key2635, -6), (key2789, -6), (key2855, -6), (key2855, -6), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow8306 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2789, -6), (key2855, -6), (key2626, 2), (key2610, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow8307 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2855, -6), (key2789, -6), (key2626, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow8308 : Integer.Sparse Key := [(key2789, -6), (key2635, -6), (key2855, -6), (key2855, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow8309 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2635, -6), (key2855, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow8310 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2855, -6), (key2635, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow8311 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2789, -6), (key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow8312 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2855, -6), (key2789, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow8313 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2635, -6), (key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow8314 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2855, -6), (key2635, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow8315 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2635, -6), (key2789, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow8316 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2789, -6), (key2635, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow8317 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2570, -6), (key2575, -6), (key2376, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2501, 2)]

def rawRow8318 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2568, -6), (key2575, -6), (key2376, 2), (key2388, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2435, 2), (key2501, 2)]

def rawRow8319 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2568, -6), (key2575, -6), (key2388, 2), (key2376, 2), (key2376, 2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, 2), (key2501, 2), (key2435, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8320 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2575, -6), (key2570, -6), (key2404, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2376, 2), (key2470, 2), (key2470, 2), (key2501, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2478, 2)]

def rawRow8321 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2568, -6), (key2570, -6), (key2404, 2), (key2435, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2388, 2), (key2478, 2)]

def rawRow8322 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2568, -6), (key2570, -6), (key2435, 2), (key2404, 2), (key2404, 2), (key2501, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2376, 2), (key2478, 2), (key2478, 2), (key2388, 2)]

def rawRow8323 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2575, -6), (key2568, -6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2376, 2), (key2404, 2), (key2470, 2)]

def rawRow8324 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2575, -6), (key2568, -6), (key2478, 2), (key2470, 2), (key2501, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2376, 2), (key2470, 2), (key2404, 2)]

def rawRow8325 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2570, -6), (key2568, -6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2404, 2), (key2376, 2), (key2470, 2)]

def rawRow8326 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2570, -6), (key2568, -6), (key2501, 2), (key2470, 2), (key2478, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2404, 2), (key2470, 2), (key2376, 2)]

def rawRow8327 : Integer.Sparse Key := [(key2570, -6), (key2575, -6), (key2568, -6), (key2568, -6), (key2478, 2), (key2501, 2), (key2470, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2470, 2), (key2376, 2), (key2404, 2)]

def rawRow8328 : Integer.Sparse Key := [(key2575, -6), (key2570, -6), (key2568, -6), (key2568, -6), (key2501, 2), (key2478, 2), (key2470, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2470, 2), (key2404, 2), (key2376, 2)]

def rawRow8341 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

def rawRow8342 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

def rawRow8343 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

def rawRow8344 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

def rawRow8345 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

def rawRow8346 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

def rawRow8347 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

def rawRow8348 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

def rawRow8349 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

def rawRow8350 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

def rawRow8351 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

def rawRow8352 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

def rawRow8353 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2873, 6)]

def rawRow8354 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2764, 6)]

def rawRow8355 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2873, 6)]

def rawRow8356 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2585, 6)]

def rawRow8357 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2764, 6)]

def rawRow8358 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2585, 6)]

def rawRow8359 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

def rawRow8360 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

def rawRow8361 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

def rawRow8362 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

def rawRow8363 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

def rawRow8364 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

def rawRow8365 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

def rawRow8366 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

def rawRow8367 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

def rawRow8368 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

def rawRow8369 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

def rawRow8370 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

def rawRow8371 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

def rawRow8372 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

def rawRow8373 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

def rawRow8374 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

def rawRow8375 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

def rawRow8376 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

def rawRow8413 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1327, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1919, -2), (key1625, -2), (key1921, -2), (key1445, -2), (key1634, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1352, 1), (key1327, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1541, 1), (key1897, 1), (key1557, 1), (key1900, 1), (key1419, 1), (key1473, 1), (key1568, 1), (key1904, 1), (key1684, 1), (key1921, 1), (key1445, 1), (key1481, 1), (key1594, 1), (key1912, 1), (key1690, 1), (key1927, 1)]

def rawRow8414 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1327, -2), (key1427, -2), (key1419, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1625, -2), (key1445, -2), (key1927, -2), (key1634, -2), (key1299, 1), (key1291, 1), (key1352, 1), (key1311, 1), (key1355, 1), (key1327, 1), (key1394, 1), (key1386, 1), (key1897, 1), (key1541, 1), (key1900, 1), (key1557, 1), (key1473, 1), (key1419, 1), (key1904, 1), (key1568, 1), (key1921, 1), (key1684, 1), (key1481, 1), (key1445, 1), (key1912, 1), (key1594, 1), (key1927, 1), (key1690, 1)]

def rawRow8415 : Integer.Sparse Key := [(key1311, -2), (key1327, -2), (key1319, -2), (key1617, -2), (key1625, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1634, -2), (key1445, -2), (key1927, -2), (key1311, 1), (key1327, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1541, 1), (key1557, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1568, 1), (key1684, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1594, 1), (key1690, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1912, 1)]

def rawRow8416 : Integer.Sparse Key := [(key1327, -2), (key1311, -2), (key1319, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1919, -2), (key1427, -2), (key1634, -2), (key1927, -2), (key1445, -2), (key1327, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1352, 1), (key1299, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1897, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1904, 1), (key1473, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1912, 1), (key1481, 1)]

def rawRow8417 : Integer.Sparse Key := [(key1319, -2), (key1327, -2), (key1311, -2), (key1919, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1419, -2), (key1617, -2), (key1927, -2), (key1445, -2), (key1634, -2), (key1352, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1291, 1), (key1311, 1), (key1897, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1386, 1), (key1541, 1), (key1904, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1419, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1445, 1), (key1594, 1)]

def rawRow8418 : Integer.Sparse Key := [(key1327, -2), (key1319, -2), (key1311, -2), (key1921, -2), (key1919, -2), (key1625, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1927, -2), (key1634, -2), (key1445, -2), (key1355, 1), (key1352, 1), (key1327, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1900, 1), (key1897, 1), (key1557, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1921, 1), (key1904, 1), (key1684, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1912, 1), (key1690, 1), (key1481, 1), (key1594, 1), (key1445, 1)]

def rawRow8419 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1919, -2), (key1634, -2), (key1927, -2), (key1327, -2), (key1625, -2), (key1921, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1897, 1), (key1690, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

def rawRow8420 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1319, -2), (key1311, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1634, -2), (key1327, -2), (key1921, -2), (key1625, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1352, 1), (key1311, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1690, 1), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

def rawRow8421 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1617, -2), (key1634, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1625, -2), (key1327, -2), (key1921, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1541, 1), (key1690, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

def rawRow8422 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1919, -2), (key1319, -2), (key1625, -2), (key1921, -2), (key1327, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1897, 1), (key1352, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

def rawRow8423 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1919, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1311, -2), (key1617, -2), (key1921, -2), (key1327, -2), (key1625, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1897, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1311, 1), (key1541, 1), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

def rawRow8424 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1927, -2), (key1919, -2), (key1634, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1921, -2), (key1625, -2), (key1327, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1897, 1), (key1690, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

def rawRow8425 : Integer.Sparse Key := [(key1617, -2), (key1625, -2), (key1634, -2), (key1311, -2), (key1327, -2), (key1419, -2), (key1921, -2), (key1445, -2), (key1927, -2), (key1319, -2), (key1427, -2), (key1919, -2), (key1541, 1), (key1557, 1), (key1568, 1), (key1684, 1), (key1594, 1), (key1690, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1921, 1), (key1445, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1900, 1), (key1481, 1), (key1912, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1897, 1), (key1473, 1), (key1904, 1)]

def rawRow8426 : Integer.Sparse Key := [(key1625, -2), (key1617, -2), (key1634, -2), (key1327, -2), (key1311, -2), (key1921, -2), (key1419, -2), (key1927, -2), (key1445, -2), (key1319, -2), (key1919, -2), (key1427, -2), (key1557, 1), (key1541, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1594, 1), (key1327, 1), (key1311, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1445, 1), (key1355, 1), (key1291, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1481, 1), (key1352, 1), (key1299, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1473, 1)]

def rawRow8427 : Integer.Sparse Key := [(key1617, -2), (key1634, -2), (key1625, -2), (key1419, -2), (key1445, -2), (key1311, -2), (key1927, -2), (key1327, -2), (key1921, -2), (key1427, -2), (key1319, -2), (key1919, -2), (key1568, 1), (key1594, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1419, 1), (key1445, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1386, 1), (key1481, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1394, 1), (key1473, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1897, 1)]

def rawRow8428 : Integer.Sparse Key := [(key1634, -2), (key1617, -2), (key1625, -2), (key1445, -2), (key1419, -2), (key1927, -2), (key1311, -2), (key1921, -2), (key1327, -2), (key1427, -2), (key1919, -2), (key1319, -2), (key1594, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1684, 1), (key1557, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1921, 1), (key1327, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1900, 1), (key1355, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1897, 1), (key1352, 1)]

def rawRow8429 : Integer.Sparse Key := [(key1625, -2), (key1634, -2), (key1617, -2), (key1921, -2), (key1927, -2), (key1327, -2), (key1445, -2), (key1311, -2), (key1419, -2), (key1919, -2), (key1319, -2), (key1427, -2), (key1684, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1541, 1), (key1568, 1), (key1921, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1311, 1), (key1419, 1), (key1900, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1291, 1), (key1386, 1), (key1897, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1299, 1), (key1394, 1)]

def rawRow8430 : Integer.Sparse Key := [(key1634, -2), (key1625, -2), (key1617, -2), (key1927, -2), (key1921, -2), (key1445, -2), (key1327, -2), (key1419, -2), (key1311, -2), (key1919, -2), (key1427, -2), (key1319, -2), (key1690, 1), (key1684, 1), (key1594, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1921, 1), (key1445, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1912, 1), (key1900, 1), (key1481, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1904, 1), (key1897, 1), (key1473, 1), (key1352, 1), (key1394, 1), (key1299, 1)]

def rawRow8431 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1319, -2), (key1327, -2), (key1427, -2), (key1625, -2), (key1445, -2), (key1634, -2), (key1311, -2), (key1419, -2), (key1617, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow8432 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1327, -2), (key1319, -2), (key1625, -2), (key1427, -2), (key1634, -2), (key1445, -2), (key1311, -2), (key1617, -2), (key1419, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow8433 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1427, -2), (key1445, -2), (key1319, -2), (key1634, -2), (key1327, -2), (key1625, -2), (key1419, -2), (key1311, -2), (key1617, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow8434 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1445, -2), (key1427, -2), (key1634, -2), (key1319, -2), (key1625, -2), (key1327, -2), (key1419, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow8435 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1625, -2), (key1634, -2), (key1327, -2), (key1445, -2), (key1319, -2), (key1427, -2), (key1617, -2), (key1311, -2), (key1419, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow8436 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1634, -2), (key1625, -2), (key1445, -2), (key1327, -2), (key1427, -2), (key1319, -2), (key1617, -2), (key1419, -2), (key1311, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow8437 : Integer.Sparse Key := [(key1352, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1473, -2), (key1682, -2), (key1682, -2), (key1684, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1690, -2), (key1299, 1), (key1299, 1), (key1319, 1), (key1319, 1), (key1327, 1), (key1327, 1), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1557, 1), (key1557, 1), (key1427, 1), (key1427, 1), (key1576, 1), (key1576, 1), (key1625, 1), (key1625, 1), (key1445, 1), (key1445, 1), (key1594, 1), (key1594, 1), (key1634, 1), (key1634, 1)]

def rawRow8438 : Integer.Sparse Key := [(key1352, -2), (key1355, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1481, -2), (key1690, -2), (key1319, 1), (key1327, 1), (key1299, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1594, 1)]

def rawRow8439 : Integer.Sparse Key := [(key1355, -2), (key1352, -2), (key1352, -2), (key1684, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1473, -2), (key1690, -2), (key1690, -2), (key1481, -2), (key1327, 1), (key1319, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1299, 1), (key1557, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1625, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1427, 1), (key1634, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1594, 1), (key1445, 1)]

def rawRow8440 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1352, -2), (key1682, -2), (key1682, -2), (key1690, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1684, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1319, 1), (key1319, 1), (key1549, 1), (key1549, 1), (key1634, 1), (key1634, 1), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

def rawRow8441 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1355, -2), (key1684, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

def rawRow8442 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1690, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1352, -2), (key1684, -2), (key1684, -2), (key1355, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1634, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1319, 1), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

def rawRow8443 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

def rawRow8444 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1355, -2), (key1352, -2), (key1684, -2), (key1473, -2), (key1690, -2), (key1481, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

def rawRow8445 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

def rawRow8446 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1481, -2), (key1473, -2), (key1690, -2), (key1352, -2), (key1684, -2), (key1355, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

def rawRow8447 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1684, -2), (key1690, -2), (key1355, -2), (key1481, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1473, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8448 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1690, -2), (key1684, -2), (key1481, -2), (key1355, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1352, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

def rawRow8485 : Integer.Sparse Key := [(key1254, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1263, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1835, -2)]

def rawRow8486 : Integer.Sparse Key := [(key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

def rawRow8487 : Integer.Sparse Key := [(key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1646, -2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

def rawRow8488 : Integer.Sparse Key := [(key1804, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1254, 2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

def rawRow8489 : Integer.Sparse Key := [(key1254, 2), (key1263, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1646, 2), (key1763, 2), (key1763, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1529, -2), (key1607, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1804, -2)]

def rawRow8490 : Integer.Sparse Key := [(key1263, 2), (key1254, 2), (key1263, 2), (key1646, 2), (key1529, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1254, -2), (key1263, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2)]

def rawRow8491 : Integer.Sparse Key := [(key1263, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1646, 2), (key1529, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1763, 2), (key1263, -2), (key1254, -2), (key1254, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1529, -2), (key1804, -2), (key1804, -2), (key1763, -2)]

def rawRow8492 : Integer.Sparse Key := [(key1529, 2), (key1763, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1263, 2), (key1263, 2), (key1646, 2), (key1646, 2), (key1835, 2), (key1835, 2), (key1529, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1254, -2), (key1607, -2), (key1607, -2), (key1804, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

def rawRow8493 : Integer.Sparse Key := [(key1763, 2), (key1529, 2), (key1763, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1529, -2), (key1763, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

def rawRow8494 : Integer.Sparse Key := [(key1763, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1263, 2), (key1763, -2), (key1529, -2), (key1529, -2), (key1804, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1254, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

def rawRow8495 : Integer.Sparse Key := [(key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1835, 2), (key1254, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1763, 2), (key1804, 2), (key1607, -2), (key1646, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1254, -2), (key1529, -2), (key1607, -2)]

def rawRow8496 : Integer.Sparse Key := [(key1646, 2), (key1835, 2), (key1804, 2), (key1263, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1763, 2), (key1646, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1646, -2), (key1529, -2), (key1804, -2), (key1763, -2), (key1254, -2), (key1607, -2), (key1529, -2)]

def rawRow8497 : Integer.Sparse Key := [(key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1835, 2), (key1529, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1263, 2), (key1646, 2), (key1607, -2), (key1804, -2), (key1646, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1529, -2), (key1254, -2), (key1607, -2)]

def rawRow8498 : Integer.Sparse Key := [(key1804, 2), (key1835, 2), (key1646, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1254, 2), (key1646, 2), (key1263, 2), (key1804, -2), (key1607, -2), (key1646, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1254, -2), (key1646, -2), (key1263, -2), (key1529, -2), (key1607, -2), (key1254, -2)]

def rawRow8499 : Integer.Sparse Key := [(key1835, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1646, 2), (key1804, 2), (key1263, 2), (key1763, 2), (key1254, 2), (key1529, 2), (key1646, -2), (key1804, -2), (key1607, -2), (key1646, -2), (key1804, -2), (key1263, -2), (key1763, -2), (key1254, -2), (key1529, -2), (key1607, -2), (key1254, -2), (key1529, -2)]

def rawRow8500 : Integer.Sparse Key := [(key1835, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1804, 2), (key1646, 2), (key1763, 2), (key1263, 2), (key1529, 2), (key1254, 2), (key1804, -2), (key1646, -2), (key1607, -2), (key1804, -2), (key1646, -2), (key1763, -2), (key1263, -2), (key1529, -2), (key1254, -2), (key1607, -2), (key1529, -2), (key1254, -2)]

def rawRow8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 6), (key425, 6), (key425, 6)]

def rawRow8502 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key205, 6), (key425, 6), (key425, 6)]

def rawRow8503 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key205, 6), (key425, 6)]

def rawRow8504 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key425, 6), (key205, 6)]

def rawRow8505 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key374, 6), (key425, 6), (key425, 6)]

def rawRow8506 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key374, 6), (key425, 6)]

def rawRow8507 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key425, 6), (key374, 6)]

def rawRow8508 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key205, 6), (key425, 6), (key425, 6)]

def rawRow8509 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key205, 6), (key425, 6)]

def rawRow8510 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key425, 6), (key205, 6)]

def rawRow8511 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key374, 6), (key425, 6)]

def rawRow8512 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key425, 6), (key374, 6)]

def rawRow8513 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key205, 6), (key425, 6)]

def rawRow8514 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key425, 6), (key205, 6)]

def rawRow8515 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key16, 6), (key374, 6)]

def rawRow8516 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key41, 6), (key205, 6)]

def rawRow8517 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key45, -6), (key70, -6), (key20, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key133, 2)]

def rawRow8518 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key70, -6), (key45, -6), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2)]

def rawRow8519 : Integer.Sparse Key := [(key45, -6), (key70, -6), (key45, -6), (key45, -6), (key102, 2), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2)]

def rawRow8520 : Integer.Sparse Key := [(key70, -6), (key45, -6), (key45, -6), (key45, -6), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2)]

def rawRow8521 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key111, -6), (key133, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2), (key111, 2), (key111, 2), (key70, 2), (key133, 2), (key133, 2)]

def rawRow8522 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key102, -6), (key133, -6), (key20, 2), (key31, 2), (key20, 2), (key102, 2), (key111, 2), (key45, 2), (key111, 2), (key45, 2), (key102, 2), (key133, 2), (key70, 2), (key133, 2)]

def rawRow8523 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key102, -6), (key133, -6), (key31, 2), (key20, 2), (key20, 2), (key111, 2), (key102, 2), (key111, 2), (key45, 2), (key102, 2), (key45, 2), (key133, 2), (key133, 2), (key70, 2)]

def rawRow8524 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key133, -6), (key111, -6), (key45, 2), (key45, 2), (key70, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key31, 2), (key111, 2), (key111, 2)]

def rawRow8525 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key102, -6), (key111, -6), (key45, 2), (key70, 2), (key45, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key111, 2), (key31, 2), (key111, 2)]

def rawRow8526 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key102, -6), (key111, -6), (key70, 2), (key45, 2), (key45, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key111, 2), (key111, 2), (key31, 2)]

def rawRow8527 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key133, -6), (key102, -6), (key102, 2), (key111, 2), (key133, 2), (key20, 2), (key31, 2), (key45, 2), (key111, 2), (key70, 2), (key133, 2), (key20, 2), (key45, 2), (key102, 2)]

def rawRow8528 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key133, -6), (key102, -6), (key111, 2), (key102, 2), (key133, 2), (key31, 2), (key20, 2), (key111, 2), (key45, 2), (key133, 2), (key70, 2), (key20, 2), (key102, 2), (key45, 2)]

def rawRow8529 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key111, -6), (key102, -6), (key102, 2), (key133, 2), (key111, 2), (key45, 2), (key70, 2), (key20, 2), (key133, 2), (key31, 2), (key111, 2), (key45, 2), (key20, 2), (key102, 2)]

def rawRow8530 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key111, -6), (key102, -6), (key133, 2), (key102, 2), (key111, 2), (key70, 2), (key45, 2), (key133, 2), (key20, 2), (key111, 2), (key31, 2), (key45, 2), (key102, 2), (key20, 2)]

def rawRow8531 : Integer.Sparse Key := [(key111, -6), (key133, -6), (key102, -6), (key102, -6), (key111, 2), (key133, 2), (key102, 2), (key111, 2), (key133, 2), (key31, 2), (key70, 2), (key20, 2), (key45, 2), (key102, 2), (key20, 2), (key45, 2)]

def rawRow8532 : Integer.Sparse Key := [(key133, -6), (key111, -6), (key102, -6), (key102, -6), (key133, 2), (key111, 2), (key102, 2), (key133, 2), (key111, 2), (key70, 2), (key31, 2), (key45, 2), (key20, 2), (key102, 2), (key45, 2), (key20, 2)]

def rawRow8533 : Integer.Sparse Key := [(key1287, -6), (key1564, -6), (key1564, -6), (key1564, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

def rawRow8534 : Integer.Sparse Key := [(key1564, -6), (key1287, -6), (key1564, -6), (key1564, -6), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow8535 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1287, -6), (key1564, -6), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

def rawRow8536 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1564, -6), (key1287, -6), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

def rawRow8537 : Integer.Sparse Key := [(key1307, -6), (key1537, -6), (key1613, -6), (key1613, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1415, 2), (key1537, 2), (key1537, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2)]

def rawRow8538 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1537, -6), (key1613, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1537, 2), (key1564, 2)]

def rawRow8539 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1613, -6), (key1537, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1415, 2), (key1382, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1564, 2), (key1537, 2)]

def rawRow8540 : Integer.Sparse Key := [(key1537, -6), (key1307, -6), (key1613, -6), (key1613, -6), (key1382, 2), (key1537, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1564, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow8541 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1307, -6), (key1613, -6), (key1537, 2), (key1382, 2), (key1537, 2), (key1564, 2), (key1287, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

def rawRow8542 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1613, -6), (key1307, -6), (key1537, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1564, 2), (key1287, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

def rawRow8543 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1537, -6), (key1613, -6), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1613, 2), (key1287, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1537, 2), (key1564, 2)]

def rawRow8544 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1613, -6), (key1537, -6), (key1415, 2), (key1613, 2), (key1564, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1382, 2), (key1564, 2), (key1537, 2)]

def rawRow8545 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1307, -6), (key1613, -6), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1613, 2), (key1382, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1307, 2), (key1415, 2)]

def rawRow8546 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1613, -6), (key1307, -6), (key1564, 2), (key1613, 2), (key1415, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1287, 2), (key1415, 2), (key1307, 2)]

def rawRow8547 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1307, -6), (key1537, -6), (key1613, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1415, 2), (key1564, 2), (key1307, 2), (key1537, 2), (key1287, 2), (key1382, 2)]

def rawRow8548 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1537, -6), (key1307, -6), (key1613, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1564, 2), (key1415, 2), (key1537, 2), (key1307, 2), (key1382, 2), (key1287, 2)]

def rawRow8549 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1914, 2)]

def rawRow8550 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2)]

def rawRow8551 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2)]

def rawRow8552 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2)]

def rawRow8553 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1677, -6), (key1914, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1677, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1914, 2)]

def rawRow8554 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1603, -6), (key1914, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1892, 2), (key1914, 2)]

def rawRow8555 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1603, -6), (key1914, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1677, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1525, 2), (key1914, 2), (key1914, 2), (key1892, 2)]

def rawRow8556 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1914, -6), (key1677, -6), (key1525, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1677, 2)]

def rawRow8557 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1603, -6), (key1677, -6), (key1525, 2), (key1892, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1269, 2), (key1677, 2)]

def rawRow8558 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1603, -6), (key1677, -6), (key1892, 2), (key1525, 2), (key1525, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1677, 2), (key1677, 2), (key1269, 2)]

def rawRow8559 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1914, -6), (key1603, -6), (key1603, 2), (key1677, 2), (key1914, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1250, 2), (key1525, 2), (key1603, 2)]

def rawRow8560 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1914, -6), (key1603, -6), (key1677, 2), (key1603, 2), (key1914, 2), (key1269, 2), (key1250, 2), (key1677, 2), (key1525, 2), (key1914, 2), (key1892, 2), (key1250, 2), (key1603, 2), (key1525, 2)]

def rawRow8561 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1677, -6), (key1603, -6), (key1603, 2), (key1914, 2), (key1677, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1525, 2), (key1250, 2), (key1603, 2)]

def rawRow8562 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1677, -6), (key1603, -6), (key1914, 2), (key1603, 2), (key1677, 2), (key1892, 2), (key1525, 2), (key1914, 2), (key1250, 2), (key1677, 2), (key1269, 2), (key1525, 2), (key1603, 2), (key1250, 2)]

def rawRow8563 : Integer.Sparse Key := [(key1677, -6), (key1914, -6), (key1603, -6), (key1603, -6), (key1677, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1914, 2), (key1269, 2), (key1892, 2), (key1250, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

def rawRow8564 : Integer.Sparse Key := [(key1914, -6), (key1677, -6), (key1603, -6), (key1603, -6), (key1914, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1892, 2), (key1269, 2), (key1525, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1250, 2)]

def rawRow8565 : Integer.Sparse Key := [(key1289, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1902, -2), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1)]

def rawRow8566 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1)]

def rawRow8567 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1)]

def rawRow8568 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1)]

def rawRow8569 : Integer.Sparse Key := [(key1309, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1539, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1)]

def rawRow8570 : Integer.Sparse Key := [(key1309, -2), (key1350, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1)]

def rawRow8571 : Integer.Sparse Key := [(key1350, -2), (key1309, -2), (key1309, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1)]

def rawRow8572 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1309, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1)]

def rawRow8573 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1)]

def rawRow8574 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1)]

def rawRow8575 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8576 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1350, -2), (key1309, -2), (key1680, -2), (key1539, -2), (key1917, -2), (key1895, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1)]

def rawRow8577 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1)]

def rawRow8578 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1895, -2), (key1539, -2), (key1917, -2), (key1309, -2), (key1680, -2), (key1350, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1)]

def rawRow8579 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1350, -2), (key1895, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1)]

def rawRow8580 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1895, -2), (key1350, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1)]

def rawRow8581 : Integer.Sparse Key := [(key1523, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1601, 6)]

def rawRow8582 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

def rawRow8583 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

def rawRow8584 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

def rawRow8585 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1523, 6), (key1601, 6), (key1601, 6)]

def rawRow8586 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1523, 6), (key1601, 6)]

def rawRow8587 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1523, 6)]

def rawRow8588 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

def rawRow8589 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

def rawRow8590 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

def rawRow8591 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1523, 6), (key1601, 6)]

def rawRow8592 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1523, 6)]

def rawRow8593 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1248, 6), (key1601, 6)]

def rawRow8594 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1601, 6), (key1248, 6)]

def rawRow8595 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1523, 6)]

def rawRow8596 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1523, 6), (key1248, 6)]

def rawRow8597 : Integer.Sparse Key := [(key1384, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1895, -2), (key1289, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1902, 2)]

def rawRow8598 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2)]

def rawRow8599 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, 2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2), (key1566, 2)]

def rawRow8600 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2)]

def rawRow8601 : Integer.Sparse Key := [(key1417, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1917, -2), (key1309, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1539, 2), (key1615, 2), (key1615, 2), (key1680, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1917, 2)]

def rawRow8602 : Integer.Sparse Key := [(key1417, -2), (key1471, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1902, -2), (key1917, -2), (key1309, 2), (key1350, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1895, 2), (key1917, 2)]

def rawRow8603 : Integer.Sparse Key := [(key1471, -2), (key1417, -2), (key1417, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1566, -2), (key1917, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1309, 2), (key1309, 2), (key1680, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1539, 2), (key1917, 2), (key1917, 2), (key1895, 2)]

def rawRow8604 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1539, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1309, 2), (key1615, 2), (key1615, 2), (key1917, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1680, 2)]

def rawRow8605 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1539, 2), (key1895, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1350, 2), (key1680, 2)]

def rawRow8606 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1417, -2), (key1680, -2), (key1680, -2), (key1471, -2), (key1895, 2), (key1539, 2), (key1539, 2), (key1917, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1309, 2), (key1680, 2), (key1680, 2), (key1350, 2)]

def rawRow8607 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1615, 2), (key1680, 2), (key1917, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1309, 2), (key1539, 2), (key1615, 2)]

def rawRow8608 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1471, -2), (key1417, -2), (key1680, -2), (key1566, -2), (key1917, -2), (key1902, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1680, 2), (key1615, 2), (key1917, 2), (key1350, 2), (key1309, 2), (key1680, 2), (key1539, 2), (key1917, 2), (key1895, 2), (key1309, 2), (key1615, 2), (key1539, 2)]

def rawRow8609 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1615, 2), (key1917, 2), (key1680, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1539, 2), (key1309, 2), (key1615, 2)]

def rawRow8610 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1902, -2), (key1566, -2), (key1917, -2), (key1417, -2), (key1680, -2), (key1471, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1917, 2), (key1615, 2), (key1680, 2), (key1895, 2), (key1539, 2), (key1917, 2), (key1309, 2), (key1680, 2), (key1350, 2), (key1539, 2), (key1615, 2), (key1309, 2)]

def rawRow8611 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1471, -2), (key1902, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1566, -2), (key1680, 2), (key1917, 2), (key1615, 2), (key1680, 2), (key1917, 2), (key1350, 2), (key1895, 2), (key1309, 2), (key1539, 2), (key1615, 2), (key1309, 2), (key1539, 2)]

def rawRow8612 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1902, -2), (key1471, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1417, -2), (key1917, 2), (key1680, 2), (key1615, 2), (key1917, 2), (key1680, 2), (key1895, 2), (key1350, 2), (key1539, 2), (key1309, 2), (key1615, 2), (key1539, 2), (key1309, 2)]

def rawRow8613 : Integer.Sparse Key := [(key238, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key417, -2), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1)]

def rawRow8614 : Integer.Sparse Key := [(key408, -2), (key408, -2), (key417, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1)]

def rawRow8615 : Integer.Sparse Key := [(key408, -2), (key417, -2), (key408, -2), (key408, -2), (key417, -2), (key238, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key408, -2), (key437, 1), (key449, 1), (key387, 1), (key449, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key437, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key250, 1), (key437, 1), (key250, 1), (key387, 1)]

def rawRow8616 : Integer.Sparse Key := [(key417, -2), (key408, -2), (key408, -2), (key417, -2), (key408, -2), (key417, -2), (key238, -2), (key408, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key449, 1), (key437, 1), (key449, 1), (key387, 1), (key437, 1), (key387, 1), (key449, 1), (key437, 1), (key449, 1), (key250, 1), (key437, 1), (key250, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key437, 1), (key387, 1), (key437, 1), (key250, 1), (key387, 1), (key250, 1)]

def rawRow8617 : Integer.Sparse Key := [(key250, -2), (key250, -2), (key259, -2), (key318, -2), (key318, -2), (key437, -2), (key437, -2), (key441, -2), (key441, -2), (key327, -2), (key449, -2), (key449, -2), (key238, 1), (key238, 1), (key250, 1), (key250, 1), (key259, 1), (key259, 1), (key304, 1), (key304, 1), (key387, 1), (key387, 1), (key396, 1), (key396, 1), (key318, 1), (key318, 1), (key408, 1), (key408, 1), (key441, 1), (key441, 1), (key327, 1), (key327, 1), (key417, 1), (key417, 1), (key449, 1), (key449, 1)]

def rawRow8618 : Integer.Sparse Key := [(key250, -2), (key259, -2), (key250, -2), (key437, -2), (key441, -2), (key318, -2), (key441, -2), (key318, -2), (key437, -2), (key449, -2), (key327, -2), (key449, -2), (key250, 1), (key259, 1), (key238, 1), (key259, 1), (key238, 1), (key250, 1), (key387, 1), (key396, 1), (key304, 1), (key396, 1), (key304, 1), (key387, 1), (key408, 1), (key441, 1), (key318, 1), (key441, 1), (key318, 1), (key408, 1), (key417, 1), (key449, 1), (key327, 1), (key449, 1), (key327, 1), (key417, 1)]

def rawRow8619 : Integer.Sparse Key := [(key259, -2), (key250, -2), (key250, -2), (key441, -2), (key437, -2), (key441, -2), (key318, -2), (key437, -2), (key318, -2), (key449, -2), (key449, -2), (key327, -2), (key259, 1), (key250, 1), (key259, 1), (key238, 1), (key250, 1), (key238, 1), (key396, 1), (key387, 1), (key396, 1), (key304, 1), (key387, 1), (key304, 1), (key441, 1), (key408, 1), (key441, 1), (key318, 1), (key408, 1), (key318, 1), (key449, 1), (key417, 1), (key449, 1), (key327, 1), (key417, 1), (key327, 1)]

def rawRow8620 : Integer.Sparse Key := [(key318, -2), (key318, -2), (key327, -2), (key250, -2), (key250, -2), (key437, -2), (key437, -2), (key449, -2), (key449, -2), (key259, -2), (key441, -2), (key441, -2), (key304, 1), (key304, 1), (key318, 1), (key318, 1), (key327, 1), (key327, 1), (key238, 1), (key238, 1), (key408, 1), (key408, 1), (key417, 1), (key417, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key259, 1), (key259, 1), (key396, 1), (key396, 1), (key441, 1), (key441, 1)]

def rawRow8621 : Integer.Sparse Key := [(key318, -2), (key327, -2), (key318, -2), (key437, -2), (key449, -2), (key250, -2), (key449, -2), (key250, -2), (key437, -2), (key441, -2), (key259, -2), (key441, -2), (key318, 1), (key327, 1), (key304, 1), (key327, 1), (key304, 1), (key318, 1), (key408, 1), (key417, 1), (key238, 1), (key417, 1), (key238, 1), (key408, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key396, 1), (key441, 1), (key259, 1), (key441, 1), (key259, 1), (key396, 1)]

def rawRow8622 : Integer.Sparse Key := [(key327, -2), (key318, -2), (key318, -2), (key449, -2), (key437, -2), (key449, -2), (key250, -2), (key437, -2), (key250, -2), (key441, -2), (key441, -2), (key259, -2), (key327, 1), (key318, 1), (key327, 1), (key304, 1), (key318, 1), (key304, 1), (key417, 1), (key408, 1), (key417, 1), (key238, 1), (key408, 1), (key238, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key441, 1), (key396, 1), (key441, 1), (key259, 1), (key396, 1), (key259, 1)]

def rawRow8623 : Integer.Sparse Key := [(key437, -2), (key441, -2), (key449, -2), (key250, -2), (key259, -2), (key318, -2), (key441, -2), (key327, -2), (key449, -2), (key250, -2), (key318, -2), (key437, -2), (key387, 1), (key396, 1), (key408, 1), (key441, 1), (key417, 1), (key449, 1), (key250, 1), (key259, 1), (key318, 1), (key441, 1), (key327, 1), (key449, 1), (key238, 1), (key259, 1), (key304, 1), (key396, 1), (key327, 1), (key417, 1), (key238, 1), (key250, 1), (key304, 1), (key387, 1), (key318, 1), (key408, 1)]

def rawRow8624 : Integer.Sparse Key := [(key441, -2), (key437, -2), (key449, -2), (key259, -2), (key250, -2), (key441, -2), (key318, -2), (key449, -2), (key327, -2), (key250, -2), (key437, -2), (key318, -2), (key396, 1), (key387, 1), (key441, 1), (key408, 1), (key449, 1), (key417, 1), (key259, 1), (key250, 1), (key441, 1), (key318, 1), (key449, 1), (key327, 1), (key259, 1), (key238, 1), (key396, 1), (key304, 1), (key417, 1), (key327, 1), (key250, 1), (key238, 1), (key387, 1), (key304, 1), (key408, 1), (key318, 1)]

def rawRow8625 : Integer.Sparse Key := [(key437, -2), (key449, -2), (key441, -2), (key318, -2), (key327, -2), (key250, -2), (key449, -2), (key259, -2), (key441, -2), (key318, -2), (key250, -2), (key437, -2), (key408, 1), (key417, 1), (key387, 1), (key449, 1), (key396, 1), (key441, 1), (key318, 1), (key327, 1), (key250, 1), (key449, 1), (key259, 1), (key441, 1), (key304, 1), (key327, 1), (key238, 1), (key417, 1), (key259, 1), (key396, 1), (key304, 1), (key318, 1), (key238, 1), (key408, 1), (key250, 1), (key387, 1)]

def rawRow8626 : Integer.Sparse Key := [(key449, -2), (key437, -2), (key441, -2), (key327, -2), (key318, -2), (key449, -2), (key250, -2), (key441, -2), (key259, -2), (key318, -2), (key437, -2), (key250, -2), (key417, 1), (key408, 1), (key449, 1), (key387, 1), (key441, 1), (key396, 1), (key327, 1), (key318, 1), (key449, 1), (key250, 1), (key441, 1), (key259, 1), (key327, 1), (key304, 1), (key417, 1), (key238, 1), (key396, 1), (key259, 1), (key318, 1), (key304, 1), (key408, 1), (key238, 1), (key387, 1), (key250, 1)]

def rawRow8627 : Integer.Sparse Key := [(key441, -2), (key449, -2), (key437, -2), (key441, -2), (key449, -2), (key259, -2), (key327, -2), (key250, -2), (key318, -2), (key437, -2), (key250, -2), (key318, -2), (key441, 1), (key449, 1), (key396, 1), (key417, 1), (key387, 1), (key408, 1), (key441, 1), (key449, 1), (key259, 1), (key327, 1), (key250, 1), (key318, 1), (key396, 1), (key417, 1), (key259, 1), (key327, 1), (key238, 1), (key304, 1), (key387, 1), (key408, 1), (key250, 1), (key318, 1), (key238, 1), (key304, 1)]

def rawRow8628 : Integer.Sparse Key := [(key449, -2), (key441, -2), (key437, -2), (key449, -2), (key441, -2), (key327, -2), (key259, -2), (key318, -2), (key250, -2), (key437, -2), (key318, -2), (key250, -2), (key449, 1), (key441, 1), (key417, 1), (key396, 1), (key408, 1), (key387, 1), (key449, 1), (key441, 1), (key327, 1), (key259, 1), (key318, 1), (key250, 1), (key417, 1), (key396, 1), (key327, 1), (key259, 1), (key304, 1), (key238, 1), (key408, 1), (key387, 1), (key318, 1), (key250, 1), (key304, 1), (key238, 1)]

def rawRow8629 : Integer.Sparse Key := [(key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1350, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2)]

def rawRow8630 : Integer.Sparse Key := [(key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2)]

def rawRow8631 : Integer.Sparse Key := [(key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1350, -2), (key1471, -2)]

def rawRow8632 : Integer.Sparse Key := [(key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1471, -2), (key1350, -2)]

def rawRow8633 : Integer.Sparse Key := [(key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1), (key1289, -2), (key1309, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1539, -2), (key1539, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2)]

def rawRow8634 : Integer.Sparse Key := [(key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1309, -2), (key1289, -2), (key1309, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1566, -2)]

def rawRow8635 : Integer.Sparse Key := [(key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1), (key1309, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1615, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1539, -2)]

def rawRow8636 : Integer.Sparse Key := [(key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1), (key1384, -2), (key1539, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1309, -2), (key1309, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2)]

def rawRow8637 : Integer.Sparse Key := [(key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1417, -2)]

def rawRow8638 : Integer.Sparse Key := [(key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1), (key1539, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1615, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1417, -2), (key1309, -2)]

def rawRow8639 : Integer.Sparse Key := [(key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1289, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1539, -2), (key1566, -2)]

def rawRow8640 : Integer.Sparse Key := [(key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1), (key1417, -2), (key1615, -2), (key1566, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1384, -2), (key1566, -2), (key1539, -2)]

def rawRow8641 : Integer.Sparse Key := [(key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1384, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1309, -2), (key1417, -2)]

def rawRow8642 : Integer.Sparse Key := [(key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1), (key1566, -2), (key1615, -2), (key1417, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1289, -2), (key1417, -2), (key1309, -2)]

def rawRow8643 : Integer.Sparse Key := [(key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1), (key1615, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1417, -2), (key1566, -2), (key1309, -2), (key1539, -2), (key1289, -2), (key1384, -2)]

def rawRow8644 : Integer.Sparse Key := [(key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1), (key1615, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1566, -2), (key1417, -2), (key1539, -2), (key1309, -2), (key1384, -2), (key1289, -2)]

def rawRow8645 : Integer.Sparse Key := [(key234, -6), (key404, -6), (key404, -6), (key404, -6), (key246, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2)]

def rawRow8646 : Integer.Sparse Key := [(key404, -6), (key234, -6), (key404, -6), (key404, -6), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key433, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

def rawRow8647 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key234, -6), (key404, -6), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

def rawRow8648 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key404, -6), (key234, -6), (key433, 2), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

def rawRow8649 : Integer.Sparse Key := [(key246, -6), (key314, -6), (key433, -6), (key433, -6), (key234, 2), (key246, 2), (key246, 2), (key300, 2), (key314, 2), (key314, 2), (key383, 2), (key383, 2), (key404, 2), (key404, 2), (key433, 2), (key433, 2)]

def rawRow8650 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key314, -6), (key433, -6), (key246, 2), (key234, 2), (key246, 2), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key433, 2), (key383, 2), (key433, 2), (key383, 2), (key404, 2)]

def rawRow8651 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key433, -6), (key314, -6), (key246, 2), (key246, 2), (key234, 2), (key314, 2), (key314, 2), (key300, 2), (key433, 2), (key404, 2), (key433, 2), (key383, 2), (key404, 2), (key383, 2)]

def rawRow8652 : Integer.Sparse Key := [(key314, -6), (key246, -6), (key433, -6), (key433, -6), (key300, 2), (key314, 2), (key314, 2), (key234, 2), (key404, 2), (key404, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

def rawRow8653 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key246, -6), (key433, -6), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key234, 2), (key404, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

def rawRow8654 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key433, -6), (key246, -6), (key314, 2), (key314, 2), (key300, 2), (key404, 2), (key404, 2), (key234, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

def rawRow8655 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key314, -6), (key433, -6), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key433, 2), (key234, 2), (key246, 2), (key300, 2), (key314, 2), (key383, 2), (key404, 2)]

def rawRow8669 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key1177, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined201_part2 : Sparse := [([1, 1, 1, -1, 0, -1, 0], -9)]

end MUB6.TaoCertificate

end OAI
end


