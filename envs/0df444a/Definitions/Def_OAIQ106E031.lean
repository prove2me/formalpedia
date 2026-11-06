-- Prove2me | Definitions.Def_OAIQ106E031
-- name    : OAIQ106E031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:53:05.361213+00:00
-- url     : https://prove2.me/theorems/a1b2b0c3-7141-4b3b-9631-e1392353c213
-- title:
--   Definitions bundle OAIQ106E031 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 230 declarations of OpenAI's Lean: 230 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.rows18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_12`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_13`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_14`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_15`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_16`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_17`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_18`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_10`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_11`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_12`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_13`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_14`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_15`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_16`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_17`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_18`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_19`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_5`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_7`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_8`, `OAI.MUB6.Certificate.GramEntries.Block3.rows19_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows1_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows1_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows20_0` and 190 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block3Row1`, `MutuallyUnbiased_GramEntries_Block3Row18`, `MutuallyUnbiased_GramEntries_Block3Row19`, `MutuallyUnbiased_GramEntries_Block3Row20`, `MutuallyUnbiased_GramEntries_Block3Row21`, `MutuallyUnbiased_GramEntries_Block3Row22`, `MutuallyUnbiased_GramEntries_Block3Row23`, `MutuallyUnbiased_GramEntries_Block3Row24`, `MutuallyUnbiased_GramEntries_Block3Row25`, `MutuallyUnbiased_GramEntries_Block3Row26`, `MutuallyUnbiased_GramEntries_Block3Row5`, `MutuallyUnbiased_GramEntries_Block3Row6`, `MutuallyUnbiased_GramEntries_Block3Row7`, `MutuallyUnbiased_GramEntries_Block3Row8`.
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E029` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E029

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7372, row7373, row7374, row7375, row7376]

def rows1_1 : Fin GramFunctions.Block3.form1.size → Integer.Sparse Key := ![row7377, row7378, row7379, row7380, row7381]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_2 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9981, row9982, row9983, row9984, row9985, row9986, row9987, row9988, row9989, row9990, row9991, row9992, row9993, row9994, row9995, row9996, row9997, row9998, row9999, row10000, row10001, row10002, row10003, row10004]

def rows18_3 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10005, row10006, row10007, row10008, row10009, row10010, row10011, row10012, row10013, row10014, row10015, row10016, row10017, row10018, row10019, row10020, row10021, row10022, row10023, row10024, row10025, row10026, row10027, row10028]

def rows18_4 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10029, row10030, row10031, row10032, row10033, row10034, row10035, row10036, row10037, row10038, row10039, row10040, row10041, row10042, row10043, row10044, row10045, row10046, row10047, row10048, row10049, row10050, row10051, row10052]

def rows18_5 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10053, row10054, row10055, row10056, row10057, row10058, row10059, row10060, row10061, row10062, row10063, row10064, row10065, row10066, row10067, row10068, row10069, row10070, row10071, row10072, row10073, row10074, row10075, row10076]

def rows18_6 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10077, row10078, row10079, row10080, row10081, row10082, row10083, row10084, row10085, row10086, row10087, row10088, row10089, row10090, row10091, row10092, row10093, row10094, row10095, row10096, row10097, row10098, row10099, row10100]

def rows18_7 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10101, row10102, row10103, row10104, row10105, row10106, row10107, row10108, row10109, row10110, row10111, row10112, row10113, row10114, row10115, row10116, row10117, row10118, row10119, row10120, row10121, row10122, row10123, row10124]

def rows18_8 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10125, row10126, row10127, row10128, row10129, row10130, row10131, row10132, row10133, row10134, row10135, row10136, row10137, row10138, row10139, row10140, row10141, row10142, row10143, row10144, row10145, row10146, row10147, row10148]

def rows18_9 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10149, row10150, row10151, row10152, row10153, row10154, row10155, row10156, row10157, row10158, row10159, row10160, row10161, row10162, row10163, row10164, row10165, row10166, row10167, row10168, row10169, row10170, row10171, row10172]

def rows18_10 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10173, row10174, row10175, row10176, row10177, row10178, row10179, row10180, row10181, row10182, row10183, row10184, row10185, row10186, row10187, row10188, row10189, row10190, row10191, row10192, row10193, row10194, row10195, row10196]

def rows18_11 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10197, row10198, row10199, row10200, row10201, row10202, row10203, row10204, row10205, row10206, row10207, row10208, row10209, row10210, row10211, row10212, row10213, row10214, row10215, row10216, row10217, row10218, row10219, row10220]

def rows18_12 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10221, row10222, row10223, row10224, row10225, row10226, row10227, row10228, row10229, row10230, row10231, row10232, row10233, row10234, row10235, row10236, row10237, row10238, row10239, row10240, row10241, row10242, row10243, row10244]

def rows18_13 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10245, row10246, row10247, row10248, row10249, row10250, row10251, row10252, row10253, row10254, row10255, row10256, row10257, row10258, row10259, row10260, row10261, row10262, row10263, row10264, row10265, row10266, row10267, row10268]

def rows18_14 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10269, row10270, row10271, row10272, row10273, row10274, row10275, row10276, row10277, row10278, row10279, row10280, row10281, row10282, row10283, row10284, row10285, row10286, row10287, row10288, row10289, row10290, row10291, row10292]

def rows18_15 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10293, row10294, row10295, row10296, row10297, row10298, row10299, row10300, row10301, row10302, row10303, row10304, row10305, row10306, row10307, row10308, row10309, row10310, row10311, row10312, row10313, row10314, row10315, row10316]

def rows18_16 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10317, row10318, row10319, row10320, row10321, row10322, row10323, row10324, row10325, row10326, row10327, row10328, row10329, row10330, row10331, row10332, row10333, row10334, row10335, row10336, row10337, row10338, row10339, row10340]

def rows18_17 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10341, row10342, row10343, row10344, row10345, row10346, row10347, row10348, row10349, row10350, row10351, row10352, row10353, row10354, row10355, row10356, row10357, row10358, row10359, row10360, row10361, row10362, row10363, row10364]

def rows18_18 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row10365, row10366, row10367, row10368, row10369, row10370, row10371, row10372, row10373, row10374, row10375, row10376, row10377, row10378, row10379, row10380, row10381, row10382, row10383, row10384, row10385, row10386, row10387, row10388]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10389, row10390, row10391, row10392, row10393, row10394, row10395, row10396, row10397, row10398]

def rows19_1 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10399, row10400, row10401, row10402, row10403, row10404, row10405, row10406, row10407, row10408]

def rows19_2 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10409, row10410, row10411, row10412, row10413, row10414, row10415, row10416, row10417, row10418]

def rows19_3 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10419, row10420, row10421, row10422, row10423, row10424, row10425, row10426, row10427, row10428]

def rows19_4 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10429, row10430, row10431, row10432, row10433, row10434, row10435, row10436, row10437, row10438]

def rows19_5 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10439, row10440, row10441, row10442, row10443, row10444, row10445, row10446, row10447, row10448]

def rows19_6 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10449, row10450, row10451, row10452, row10453, row10454, row10455, row10456, row10457, row10458]

def rows19_7 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10459, row10460, row10461, row10462, row10463, row10464, row10465, row10466, row10467, row10468]

def rows19_8 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10469, row10470, row10471, row10472, row10473, row10474, row10475, row10476, row10477, row10478]

def rows19_9 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10479, row10480, row10481, row10482, row10483, row10484, row10485, row10486, row10487, row10488]

def rows19_10 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10489, row10490, row10491, row10492, row10493, row10494, row10495, row10496, row10497, row10498]

def rows19_11 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10499, row10500, row10501, row10502, row10503, row10504, row10505, row10506, row10507, row10508]

def rows19_12 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10509, row10510, row10511, row10512, row10513, row10514, row10515, row10516, row10517, row10518]

def rows19_13 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10519, row10520, row10521, row10522, row10523, row10524, row10525, row10526, row10527, row10528]

def rows19_14 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10529, row10530, row10531, row10532, row10533, row10534, row10535, row10536, row10537, row10538]

def rows19_15 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10539, row10540, row10541, row10542, row10543, row10544, row10545, row10546, row10547, row10548]

def rows19_16 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10549, row10550, row10551, row10552, row10553, row10554, row10555, row10556, row10557, row10558]

def rows19_17 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10559, row10560, row10561, row10562, row10563, row10564, row10565, row10566, row10567, row10568]

def rows19_18 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10569, row10570, row10571, row10572, row10573, row10574, row10575, row10576, row10577, row10578]

def rows19_19 : Fin GramFunctions.Block3.form19.size → Integer.Sparse Key := ![row10579, row10580, row10581, row10582, row10583, row10584, row10585, row10586, row10587, row10588]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10589, row10590, row10591, row10592, row10593]

def rows20_1 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10594, row10595, row10596, row10597, row10598]

def rows20_2 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10599, row10600, row10601, row10602, row10603]

def rows20_3 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10604, row10605, row10606, row10607, row10608]

def rows20_4 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10609, row10610, row10611, row10612, row10613]

def rows20_5 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10614, row10615, row10616, row10617, row10618]

def rows20_6 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10619, row10620, row10621, row10622, row10623]

def rows20_7 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10624, row10625, row10626, row10627, row10628]

def rows20_8 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10629, row10630, row10631, row10632, row10633]

def rows20_9 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10634, row10635, row10636, row10637, row10638]

def rows20_10 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10639, row10640, row10641, row10642, row10643]

def rows20_11 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10644, row10645, row10646, row10647, row10648]

def rows20_12 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10649, row10650, row10651, row10652, row10653]

def rows20_13 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10654, row10655, row10656, row10657, row10658]

def rows20_14 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10659, row10660, row10661, row10662, row10663]

def rows20_15 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10664, row10665, row10666, row10667, row10668]

def rows20_16 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10669, row10670, row10671, row10672, row10673]

def rows20_17 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10674, row10675, row10676, row10677, row10678]

def rows20_18 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10679, row10680, row10681, row10682, row10683]

def rows20_19 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10684, row10685, row10686, row10687, row10688]

def rows20_20 : Fin GramFunctions.Block3.form20.size → Integer.Sparse Key := ![row10689, row10690, row10691, row10692, row10693]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows21_0 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717, row10718, row10719, row10720, row10721, row10722, row10723, row10724, row10725, row10726, row10727, row10728, row10729]

def rows21_1 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753, row10754, row10755, row10756, row10757, row10758, row10759, row10760, row10761, row10762, row10763, row10764, row10765]

def rows21_2 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789, row10790, row10791, row10792, row10793, row10794, row10795, row10796, row10797, row10798, row10799, row10800, row10801]

def rows21_3 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825, row10826, row10827, row10828, row10829, row10830, row10831, row10832, row10833, row10834, row10835, row10836, row10837]

def rows21_4 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861, row10862, row10863, row10864, row10865, row10866, row10867, row10868, row10869, row10870, row10871, row10872, row10873]

def rows21_5 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897, row10898, row10899, row10900, row10901, row10902, row10903, row10904, row10905, row10906, row10907, row10908, row10909]

def rows21_6 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933, row10934, row10935, row10936, row10937, row10938, row10939, row10940, row10941, row10942, row10943, row10944, row10945]

def rows21_7 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969, row10970, row10971, row10972, row10973, row10974, row10975, row10976, row10977, row10978, row10979, row10980, row10981]

def rows21_8 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005, row11006, row11007, row11008, row11009, row11010, row11011, row11012, row11013, row11014, row11015, row11016, row11017]

def rows21_9 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041, row11042, row11043, row11044, row11045, row11046, row11047, row11048, row11049, row11050, row11051, row11052, row11053]

def rows21_10 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077, row11078, row11079, row11080, row11081, row11082, row11083, row11084, row11085, row11086, row11087, row11088, row11089]

def rows21_11 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113, row11114, row11115, row11116, row11117, row11118, row11119, row11120, row11121, row11122, row11123, row11124, row11125]

def rows21_12 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149, row11150, row11151, row11152, row11153, row11154, row11155, row11156, row11157, row11158, row11159, row11160, row11161]

def rows21_13 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185, row11186, row11187, row11188, row11189, row11190, row11191, row11192, row11193, row11194, row11195, row11196, row11197]

def rows21_14 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221, row11222, row11223, row11224, row11225, row11226, row11227, row11228, row11229, row11230, row11231, row11232, row11233]

def rows21_15 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257, row11258, row11259, row11260, row11261, row11262, row11263, row11264, row11265, row11266, row11267, row11268, row11269]

def rows21_16 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293, row11294, row11295, row11296, row11297, row11298, row11299, row11300, row11301, row11302, row11303, row11304, row11305]

def rows21_17 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329, row11330, row11331, row11332, row11333, row11334, row11335, row11336, row11337, row11338, row11339, row11340, row11341]

def rows21_18 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365, row11366, row11367, row11368, row11369, row11370, row11371, row11372, row11373, row11374, row11375, row11376, row11377]

def rows21_19 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401, row11402, row11403, row11404, row11405, row11406, row11407, row11408, row11409, row11410, row11411, row11412, row11413]

def rows21_20 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437, row11438, row11439, row11440, row11441, row11442, row11443, row11444, row11445, row11446, row11447, row11448, row11449]

def rows21_21 : Fin GramFunctions.Block3.form21.size → Integer.Sparse Key := ![row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473, row11474, row11475, row11476, row11477, row11478, row11479, row11480, row11481, row11482, row11483, row11484, row11485]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows22_0 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11486, row11487, row11488, row11489, row11490, row11491, row11492, row11493, row11494, row11495, row11496, row11497, row10694, row10695, row10696, row10697, row10698, row10699, row10700, row10701, row10702, row10703, row10704, row10705, row10706, row10707, row10708, row10709, row10710, row10711, row10712, row10713, row10714, row10715, row10716, row10717]

def rows22_1 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11498, row11499, row11500, row11501, row11502, row11503, row11504, row11505, row11506, row11507, row11508, row11509, row10730, row10731, row10732, row10733, row10734, row10735, row10736, row10737, row10738, row10739, row10740, row10741, row10742, row10743, row10744, row10745, row10746, row10747, row10748, row10749, row10750, row10751, row10752, row10753]

def rows22_2 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11510, row11511, row11512, row11513, row11514, row11515, row11516, row11517, row11518, row11519, row11520, row11521, row10766, row10767, row10768, row10769, row10770, row10771, row10772, row10773, row10774, row10775, row10776, row10777, row10778, row10779, row10780, row10781, row10782, row10783, row10784, row10785, row10786, row10787, row10788, row10789]

def rows22_3 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11522, row11523, row11524, row11525, row11526, row11527, row11528, row11529, row11530, row11531, row11532, row11533, row10802, row10803, row10804, row10805, row10806, row10807, row10808, row10809, row10810, row10811, row10812, row10813, row10814, row10815, row10816, row10817, row10818, row10819, row10820, row10821, row10822, row10823, row10824, row10825]

def rows22_4 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11534, row11535, row11536, row11537, row11538, row11539, row11540, row11541, row11542, row11543, row11544, row11545, row10838, row10839, row10840, row10841, row10842, row10843, row10844, row10845, row10846, row10847, row10848, row10849, row10850, row10851, row10852, row10853, row10854, row10855, row10856, row10857, row10858, row10859, row10860, row10861]

def rows22_5 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11546, row11547, row11548, row11549, row11550, row11551, row11552, row11553, row11554, row11555, row11556, row11557, row10874, row10875, row10876, row10877, row10878, row10879, row10880, row10881, row10882, row10883, row10884, row10885, row10886, row10887, row10888, row10889, row10890, row10891, row10892, row10893, row10894, row10895, row10896, row10897]

def rows22_6 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11558, row11559, row11560, row11561, row11562, row11563, row11564, row11565, row11566, row11567, row11568, row11569, row10910, row10911, row10912, row10913, row10914, row10915, row10916, row10917, row10918, row10919, row10920, row10921, row10922, row10923, row10924, row10925, row10926, row10927, row10928, row10929, row10930, row10931, row10932, row10933]

def rows22_7 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11570, row11571, row11572, row11573, row11574, row11575, row11576, row11577, row11578, row11579, row11580, row11581, row10946, row10947, row10948, row10949, row10950, row10951, row10952, row10953, row10954, row10955, row10956, row10957, row10958, row10959, row10960, row10961, row10962, row10963, row10964, row10965, row10966, row10967, row10968, row10969]

def rows22_8 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11582, row11583, row11584, row11585, row11586, row11587, row11588, row11589, row11590, row11591, row11592, row11593, row10982, row10983, row10984, row10985, row10986, row10987, row10988, row10989, row10990, row10991, row10992, row10993, row10994, row10995, row10996, row10997, row10998, row10999, row11000, row11001, row11002, row11003, row11004, row11005]

def rows22_9 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11594, row11595, row11596, row11597, row11598, row11599, row11600, row11601, row11602, row11603, row11604, row11605, row11018, row11019, row11020, row11021, row11022, row11023, row11024, row11025, row11026, row11027, row11028, row11029, row11030, row11031, row11032, row11033, row11034, row11035, row11036, row11037, row11038, row11039, row11040, row11041]

def rows22_10 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11606, row11607, row11608, row11609, row11610, row11611, row11612, row11613, row11614, row11615, row11616, row11617, row11054, row11055, row11056, row11057, row11058, row11059, row11060, row11061, row11062, row11063, row11064, row11065, row11066, row11067, row11068, row11069, row11070, row11071, row11072, row11073, row11074, row11075, row11076, row11077]

def rows22_11 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11618, row11619, row11620, row11621, row11622, row11623, row11624, row11625, row11626, row11627, row11628, row11629, row11090, row11091, row11092, row11093, row11094, row11095, row11096, row11097, row11098, row11099, row11100, row11101, row11102, row11103, row11104, row11105, row11106, row11107, row11108, row11109, row11110, row11111, row11112, row11113]

def rows22_12 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11630, row11631, row11632, row11633, row11634, row11635, row11636, row11637, row11638, row11639, row11640, row11641, row11126, row11127, row11128, row11129, row11130, row11131, row11132, row11133, row11134, row11135, row11136, row11137, row11138, row11139, row11140, row11141, row11142, row11143, row11144, row11145, row11146, row11147, row11148, row11149]

def rows22_13 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11642, row11643, row11644, row11645, row11646, row11647, row11648, row11649, row11650, row11651, row11652, row11653, row11162, row11163, row11164, row11165, row11166, row11167, row11168, row11169, row11170, row11171, row11172, row11173, row11174, row11175, row11176, row11177, row11178, row11179, row11180, row11181, row11182, row11183, row11184, row11185]

def rows22_14 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11654, row11655, row11656, row11657, row11658, row11659, row11660, row11661, row11662, row11663, row11664, row11665, row11198, row11199, row11200, row11201, row11202, row11203, row11204, row11205, row11206, row11207, row11208, row11209, row11210, row11211, row11212, row11213, row11214, row11215, row11216, row11217, row11218, row11219, row11220, row11221]

def rows22_15 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11666, row11667, row11668, row11669, row11670, row11671, row11672, row11673, row11674, row11675, row11676, row11677, row11234, row11235, row11236, row11237, row11238, row11239, row11240, row11241, row11242, row11243, row11244, row11245, row11246, row11247, row11248, row11249, row11250, row11251, row11252, row11253, row11254, row11255, row11256, row11257]

def rows22_16 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11678, row11679, row11680, row11681, row11682, row11683, row11684, row11685, row11686, row11687, row11688, row11689, row11270, row11271, row11272, row11273, row11274, row11275, row11276, row11277, row11278, row11279, row11280, row11281, row11282, row11283, row11284, row11285, row11286, row11287, row11288, row11289, row11290, row11291, row11292, row11293]

def rows22_17 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11690, row11691, row11692, row11693, row11694, row11695, row11696, row11697, row11698, row11699, row11700, row11701, row11306, row11307, row11308, row11309, row11310, row11311, row11312, row11313, row11314, row11315, row11316, row11317, row11318, row11319, row11320, row11321, row11322, row11323, row11324, row11325, row11326, row11327, row11328, row11329]

def rows22_18 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11702, row11703, row11704, row11705, row11706, row11707, row11708, row11709, row11710, row11711, row11712, row11713, row11342, row11343, row11344, row11345, row11346, row11347, row11348, row11349, row11350, row11351, row11352, row11353, row11354, row11355, row11356, row11357, row11358, row11359, row11360, row11361, row11362, row11363, row11364, row11365]

def rows22_19 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11714, row11715, row11716, row11717, row11718, row11719, row11720, row11721, row11722, row11723, row11724, row11725, row11378, row11379, row11380, row11381, row11382, row11383, row11384, row11385, row11386, row11387, row11388, row11389, row11390, row11391, row11392, row11393, row11394, row11395, row11396, row11397, row11398, row11399, row11400, row11401]

def rows22_20 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11726, row11727, row11728, row11729, row11730, row11731, row11732, row11733, row11734, row11735, row11736, row11737, row11414, row11415, row11416, row11417, row11418, row11419, row11420, row11421, row11422, row11423, row11424, row11425, row11426, row11427, row11428, row11429, row11430, row11431, row11432, row11433, row11434, row11435, row11436, row11437]

def rows22_21 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11738, row11739, row11740, row11741, row11742, row11743, row11744, row11745, row11746, row11747, row11748, row11749, row11450, row11451, row11452, row11453, row11454, row11455, row11456, row11457, row11458, row11459, row11460, row11461, row11462, row11463, row11464, row11465, row11466, row11467, row11468, row11469, row11470, row11471, row11472, row11473]

def rows22_22 : Fin GramFunctions.Block3.form22.size → Integer.Sparse Key := ![row11750, row11751, row11752, row11753, row11754, row11755, row11756, row11757, row11758, row11759, row11760, row11761, row11762, row11763, row11764, row11765, row11766, row11767, row11768, row11769, row11770, row11771, row11772, row11773, row11774, row11775, row11776, row11777, row11778, row11779, row11780, row11781, row11782, row11783, row11784, row11785]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows23_1 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11792, row11793, row11794, row11795, row11796, row11797, row11798, row11799, row11800, row11801, row11802, row11803, row11804, row11805, row11806, row11807, row11808, row11809]

def rows23_2 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11810, row11811, row11812, row11813, row11814, row11815, row11816, row11817, row11818, row11819, row11820, row11821, row11822, row11823, row11824, row11825, row11826, row11827]

def rows23_3 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11828, row11829, row11830, row11831, row11832, row11833, row11834, row11835, row11836, row11837, row11838, row11839, row11840, row11841, row11842, row11843, row11844, row11845]

def rows23_4 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11846, row11847, row11848, row11849, row11850, row11851, row11852, row11853, row11854, row11855, row11856, row11857, row11858, row11859, row11860, row11861, row11862, row11863]

def rows23_5 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11864, row11865, row11866, row11867, row11868, row11869, row11870, row11871, row11872, row11873, row11874, row11875, row11876, row11877, row11878, row11879, row11880, row11881]

def rows23_6 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11882, row11883, row11884, row11885, row11886, row11887, row11888, row11889, row11890, row11891, row11892, row11893, row11894, row11895, row11896, row11897, row11898, row11899]

def rows23_7 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11900, row11901, row11902, row11903, row11904, row11905, row11906, row11907, row11908, row11909, row11910, row11911, row11912, row11913, row11914, row11915, row11916, row11917]

def rows23_8 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11918, row11919, row11920, row11921, row11922, row11923, row11924, row11925, row11926, row11927, row11928, row11929, row11930, row11931, row11932, row11933, row11934, row11935]

def rows23_9 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11936, row11937, row11938, row11939, row11940, row11941, row11942, row11943, row11944, row11945, row11946, row11947, row11948, row11949, row11950, row11951, row11952, row11953]

def rows23_10 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11954, row11955, row11956, row11957, row11958, row11959, row11960, row11961, row11962, row11963, row11964, row11965, row11966, row11967, row11968, row11969, row11970, row11971]

def rows23_11 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11972, row11973, row11974, row11975, row11976, row11977, row11978, row11979, row11980, row11981, row11982, row11983, row11984, row11985, row11986, row11987, row11988, row11989]

def rows23_12 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11990, row11991, row11992, row11993, row11994, row11995, row11996, row11997, row11998, row11999, row12000, row12001, row12002, row12003, row12004, row12005, row12006, row12007]

def rows23_13 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12008, row12009, row12010, row12011, row12012, row12013, row12014, row12015, row12016, row12017, row12018, row12019, row12020, row12021, row12022, row12023, row12024, row12025]

def rows23_14 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12026, row12027, row12028, row12029, row12030, row12031, row12032, row12033, row12034, row12035, row12036, row12037, row12038, row12039, row12040, row12041, row12042, row12043]

def rows23_15 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12044, row12045, row12046, row12047, row12048, row12049, row12050, row12051, row12052, row12053, row12054, row12055, row12056, row12057, row12058, row12059, row12060, row12061]

def rows23_16 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12062, row12063, row12064, row12065, row12066, row12067, row12068, row12069, row12070, row12071, row12072, row12073, row12074, row12075, row12076, row12077, row12078, row12079]

def rows23_17 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12080, row12081, row12082, row12083, row12084, row12085, row12086, row12087, row12088, row12089, row12090, row12091, row12092, row12093, row12094, row12095, row12096, row12097]

def rows23_18 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12098, row12099, row12100, row12101, row12102, row12103, row12104, row12105, row12106, row12107, row12108, row12109, row12110, row12111, row12112, row12113, row12114, row12115]

def rows23_19 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12116, row12117, row12118, row12119, row12120, row12121, row12122, row12123, row12124, row12125, row12126, row12127, row12128, row12129, row12130, row12131, row12132, row12133]

def rows23_20 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12134, row12135, row12136, row12137, row12138, row12139, row12140, row12141, row12142, row12143, row12144, row12145, row12146, row12147, row12148, row12149, row12150, row12151]

def rows23_21 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12152, row12153, row12154, row12155, row12156, row12157, row12158, row12159, row12160, row12161, row12162, row12163, row12164, row12165, row12166, row12167, row12168, row12169]

def rows23_22 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12170, row12171, row12172, row12173, row12174, row12175, row12176, row12177, row12178, row12179, row12180, row12181, row12182, row12183, row12184, row12185, row12186, row12187]

def rows23_23 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row12188, row12189, row12190, row12191, row12192, row12193, row12194, row12195, row12196, row12197, row12198, row12199, row12200, row12201, row12202, row12203, row12204, row12205]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows24_0 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12206, row12207, row12208, row12209, row12210]

def rows24_1 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12211, row12212, row12213, row12214, row12215]

def rows24_2 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12216, row12217, row12218, row12219, row12220]

def rows24_3 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12221, row12222, row12223, row12224, row12225]

def rows24_4 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12226, row12227, row12228, row12229, row12230]

def rows24_5 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12231, row12232, row12233, row12234, row12235]

def rows24_6 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12236, row12237, row12238, row12239, row12240]

def rows24_7 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12241, row12242, row12243, row12244, row12245]

def rows24_8 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12246, row12247, row12248, row12249, row12250]

def rows24_9 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12251, row12252, row12253, row12254, row12255]

def rows24_10 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12256, row12257, row12258, row12259, row12260]

def rows24_11 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12261, row12262, row12263, row12264, row12265]

def rows24_12 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12266, row12267, row12268, row12269, row12270]

def rows24_13 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12271, row12272, row12273, row12274, row12275]

def rows24_14 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12276, row12277, row12278, row12279, row12280]

def rows24_15 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12281, row12282, row12283, row12284, row12285]

def rows24_16 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12286, row12287, row12288, row12289, row12290]

def rows24_17 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12291, row12292, row12293, row12294, row12295]

def rows24_18 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12296, row12297, row12298, row12299, row12300]

def rows24_19 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12301, row12302, row12303, row12304, row12305]

def rows24_20 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12306, row12307, row12308, row12309, row12310]

def rows24_21 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12311, row12312, row12313, row12314, row12315]

def rows24_22 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12316, row12317, row12318, row12319, row12320]

def rows24_23 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12321, row12322, row12323, row12324, row12325]

def rows24_24 : Fin GramFunctions.Block3.form24.size → Integer.Sparse Key := ![row12326, row12327, row12328, row12329, row12330]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows25_0 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12331, row12332, row12333, row12334, row12335, row12336, row12337, row12338]

def rows25_1 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12339, row12340, row12341, row12342, row12343, row12344, row12345, row12346]

def rows25_2 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12347, row12348, row12349, row12350, row12351, row12352, row12353, row12354]

def rows25_3 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12355, row12356, row12357, row12358, row12359, row12360, row12361, row12362]

def rows25_4 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12363, row12364, row12365, row12366, row12367, row12368, row12369, row12370]

def rows25_5 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12371, row12372, row12373, row12374, row12375, row12376, row12377, row12378]

def rows25_6 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12379, row12380, row12381, row12382, row12383, row12384, row12385, row12386]

def rows25_7 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12387, row12388, row12389, row12390, row12391, row12392, row12393, row12394]

def rows25_8 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12395, row12396, row12397, row12398, row12399, row12400, row12401, row12402]

def rows25_9 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12403, row12404, row12405, row12406, row12407, row12408, row12409, row12410]

def rows25_10 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12411, row12412, row12413, row12414, row12415, row12416, row12417, row12418]

def rows25_11 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12419, row12420, row12421, row12422, row12423, row12424, row12425, row12426]

def rows25_12 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12427, row12428, row12429, row12430, row12431, row12432, row12433, row12434]

def rows25_13 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12435, row12436, row12437, row12438, row12439, row12440, row12441, row12442]

def rows25_14 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12443, row12444, row12445, row12446, row12447, row12448, row12449, row12450]

def rows25_15 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12451, row12452, row12453, row12454, row12455, row12456, row12457, row12458]

def rows25_16 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12459, row12460, row12461, row12462, row12463, row12464, row12465, row12466]

def rows25_17 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12467, row12468, row12469, row12470, row12471, row12472, row12473, row12474]

def rows25_18 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12475, row12476, row12477, row12478, row12479, row12480, row12481, row12482]

def rows25_19 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12483, row12484, row12485, row12486, row12487, row12488, row12489, row12490]

def rows25_20 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12491, row12492, row12493, row12494, row12495, row12496, row12497, row12498]

def rows25_21 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12499, row12500, row12501, row12502, row12503, row12504, row12505, row12506]

def rows25_22 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12507, row12508, row12509, row12510, row12511, row12512, row12513, row12514]

def rows25_23 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12515, row12516, row12517, row12518, row12519, row12520, row12521, row12522]

def rows25_24 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12523, row12524, row12525, row12526, row12527, row12528, row12529, row12530]

def rows25_25 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12531, row12532, row12533, row12534, row12535, row12536, row12537, row12538]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows26_0 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12539, row12540, row12541, row12542, row12543, row12544, row12545, row12546, row12547, row12548, row12549, row12550, row12551, row12552, row12553, row12554, row12555, row12556, row12557, row12558, row12559, row12560, row12561, row12562]

def rows26_1 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12563, row12564, row12565, row12566, row12567, row12568, row12569, row12570, row12571, row12572, row12573, row12574, row12575, row12576, row12577, row12578, row12579, row12580, row12581, row12582, row12583, row12584, row12585, row12586]

def rows26_2 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12587, row12588, row12589, row12590, row12591, row12592, row12593, row12594, row12595, row12596, row12597, row12598, row12599, row12600, row12601, row12602, row12603, row12604, row12605, row12606, row12607, row12608, row12609, row12610]

def rows26_3 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12611, row12612, row12613, row12614, row12615, row12616, row12617, row12618, row12619, row12620, row12621, row12622, row12623, row12624, row12625, row12626, row12627, row12628, row12629, row12630, row12631, row12632, row12633, row12634]

def rows26_4 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12635, row12636, row12637, row12638, row12639, row12640, row12641, row12642, row12643, row12644, row12645, row12646, row12647, row12648, row12649, row12650, row12651, row12652, row12653, row12654, row12655, row12656, row12657, row12658]

def rows26_5 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12659, row12660, row12661, row12662, row12663, row12664, row12665, row12666, row12667, row12668, row12669, row12670, row12671, row12672, row12673, row12674, row12675, row12676, row12677, row12678, row12679, row12680, row12681, row12682]

def rows26_6 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12683, row12684, row12685, row12686, row12687, row12688, row12689, row12690, row12691, row12692, row12693, row12694, row12695, row12696, row12697, row12698, row12699, row12700, row12701, row12702, row12703, row12704, row12705, row12706]

def rows26_7 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12707, row12708, row12709, row12710, row12711, row12712, row12713, row12714, row12715, row12716, row12717, row12718, row12719, row12720, row12721, row12722, row12723, row12724, row12725, row12726, row12727, row12728, row12729, row12730]

def rows26_8 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12731, row12732, row12733, row12734, row12735, row12736, row12737, row12738, row12739, row12740, row12741, row12742, row12743, row12744, row12745, row12746, row12747, row12748, row12749, row12750, row12751, row12752, row12753, row12754]

def rows26_9 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12755, row12756, row12757, row12758, row12759, row12760, row12761, row12762, row12763, row12764, row12765, row12766, row12767, row12768, row12769, row12770, row12771, row12772, row12773, row12774, row12775, row12776, row12777, row12778]

def rows26_10 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12779, row12780, row12781, row12782, row12783, row12784, row12785, row12786, row12787, row12788, row12789, row12790, row12791, row12792, row12793, row12794, row12795, row12796, row12797, row12798, row12799, row12800, row12801, row12802]

def rows26_11 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12803, row12804, row12805, row12806, row12807, row12808, row12809, row12810, row12811, row12812, row12813, row12814, row12815, row12816, row12817, row12818, row12819, row12820, row12821, row12822, row12823, row12824, row12825, row12826]

def rows26_12 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12827, row12828, row12829, row12830, row12831, row12832, row12833, row12834, row12835, row12836, row12837, row12838, row12839, row12840, row12841, row12842, row12843, row12844, row12845, row12846, row12847, row12848, row12849, row12850]

def rows26_13 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12851, row12852, row12853, row12854, row12855, row12856, row12857, row12858, row12859, row12860, row12861, row12862, row12863, row12864, row12865, row12866, row12867, row12868, row12869, row12870, row12871, row12872, row12873, row12874]

def rows26_14 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12875, row12876, row12877, row12878, row12879, row12880, row12881, row12882, row12883, row12884, row12885, row12886, row12887, row12888, row12889, row12890, row12891, row12892, row12893, row12894, row12895, row12896, row12897, row12898]

def rows26_15 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12899, row12900, row12901, row12902, row12903, row12904, row12905, row12906, row12907, row12908, row12909, row12910, row12911, row12912, row12913, row12914, row12915, row12916, row12917, row12918, row12919, row12920, row12921, row12922]

def rows26_16 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12923, row12924, row12925, row12926, row12927, row12928, row12929, row12930, row12931, row12932, row12933, row12934, row12935, row12936, row12937, row12938, row12939, row12940, row12941, row12942, row12943, row12944, row12945, row12946]

def rows26_17 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12947, row12948, row12949, row12950, row12951, row12952, row12953, row12954, row12955, row12956, row12957, row12958, row12959, row12960, row12961, row12962, row12963, row12964, row12965, row12966, row12967, row12968, row12969, row12970]

def rows26_18 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12971, row12972, row12973, row12974, row12975, row12976, row12977, row12978, row12979, row12980, row12981, row12982, row12983, row12984, row12985, row12986, row12987, row12988, row12989, row12990, row12991, row12992, row12993, row12994]

def rows26_19 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row12995, row12996, row12997, row12998, row12999, row13000, row13001, row13002, row13003, row13004, row13005, row13006, row13007, row13008, row13009, row13010, row13011, row13012, row13013, row13014, row13015, row13016, row13017, row13018]

def rows26_20 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13019, row13020, row13021, row13022, row13023, row13024, row13025, row13026, row13027, row13028, row13029, row13030, row13031, row13032, row13033, row13034, row13035, row13036, row13037, row13038, row13039, row13040, row13041, row13042]

def rows26_21 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13043, row13044, row13045, row13046, row13047, row13048, row13049, row13050, row13051, row13052, row13053, row13054, row13055, row13056, row13057, row13058, row13059, row13060, row13061, row13062, row13063, row13064, row13065, row13066]

def rows26_22 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13067, row13068, row13069, row13070, row13071, row13072, row13073, row13074, row13075, row13076, row13077, row13078, row13079, row13080, row13081, row13082, row13083, row13084, row13085, row13086, row13087, row13088, row13089, row13090]

def rows26_23 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13091, row13092, row13093, row13094, row13095, row13096, row13097, row13098, row13099, row13100, row13101, row13102, row13103, row13104, row13105, row13106, row13107, row13108, row13109, row13110, row13111, row13112, row13113, row13114]

def rows26_24 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13115, row13116, row13117, row13118, row13119, row13120, row13121, row13122, row13123, row13124, row13125, row13126, row13127, row13128, row13129, row13130, row13131, row13132, row13133, row13134, row13135, row13136, row13137, row13138]

def rows26_25 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13139, row13140, row13141, row13142, row13143, row13144, row13145, row13146, row13147, row13148, row13149, row13150, row13151, row13152, row13153, row13154, row13155, row13156, row13157, row13158, row13159, row13160, row13161, row13162]

def rows26_26 : Fin GramFunctions.Block3.form26.size → Integer.Sparse Key := ![row13163, row13164, row13165, row13166, row13167, row13168, row13169, row13170, row13171, row13172, row13173, row13174, row13175, row13176, row13177, row13178, row13179, row13180, row13181, row13182, row13183, row13184, row13185, row13186]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585, row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609]

def rows5_1 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621, row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645]

def rows5_2 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657, row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681]

def rows5_3 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693, row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717]

def rows5_4 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729, row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753]

def rows5_5 : Fin GramFunctions.Block3.form5.size → Integer.Sparse Key := ![row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765, row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7790, row7791, row7792, row7793, row7794]

def rows6_1 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7795, row7796, row7797, row7798, row7799]

def rows6_2 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7800, row7801, row7802, row7803, row7804]

def rows6_3 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7805, row7806, row7807, row7808, row7809]

def rows6_4 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7810, row7811, row7812, row7813, row7814]

def rows6_5 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7815, row7816, row7817, row7818, row7819]

def rows6_6 : Fin GramFunctions.Block3.form6.size → Integer.Sparse Key := ![row7820, row7821, row7822, row7823, row7824]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7825, row7826, row7827, row7828, row7829, row7830, row7831, row7832, row7833, row7834, row7835, row7836, row7574, row7575, row7576, row7577, row7578, row7579, row7580, row7581, row7582, row7583, row7584, row7585]

def rows7_1 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7837, row7838, row7839, row7840, row7841, row7842, row7843, row7844, row7845, row7846, row7847, row7848, row7610, row7611, row7612, row7613, row7614, row7615, row7616, row7617, row7618, row7619, row7620, row7621]

def rows7_2 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7849, row7850, row7851, row7852, row7853, row7854, row7855, row7856, row7857, row7858, row7859, row7860, row7646, row7647, row7648, row7649, row7650, row7651, row7652, row7653, row7654, row7655, row7656, row7657]

def rows7_3 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7861, row7862, row7863, row7864, row7865, row7866, row7867, row7868, row7869, row7870, row7871, row7872, row7682, row7683, row7684, row7685, row7686, row7687, row7688, row7689, row7690, row7691, row7692, row7693]

def rows7_4 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7873, row7874, row7875, row7876, row7877, row7878, row7879, row7880, row7881, row7882, row7883, row7884, row7718, row7719, row7720, row7721, row7722, row7723, row7724, row7725, row7726, row7727, row7728, row7729]

def rows7_5 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7885, row7886, row7887, row7888, row7889, row7890, row7891, row7892, row7893, row7894, row7895, row7896, row7754, row7755, row7756, row7757, row7758, row7759, row7760, row7761, row7762, row7763, row7764, row7765]

def rows7_6 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7897, row7898, row7899, row7900, row7901, row7902, row7903, row7904, row7905, row7906, row7907, row7908, row7909, row7910, row7911, row7912, row7913, row7914, row7915, row7916, row7917, row7918, row7919, row7920]

def rows7_7 : Fin GramFunctions.Block3.form7.size → Integer.Sparse Key := ![row7921, row7922, row7923, row7924, row7925, row7926, row7927, row7928, row7929, row7930, row7931, row7932, row7933, row7934, row7935, row7936, row7937, row7938, row7939, row7940, row7941, row7942, row7943, row7944]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

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

def rows8_0 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7945, row7946, row7947, row7948, row7949, row7950, row7951, row7952, row7953, row7954, row7955, row7956, row7957, row7958, row7959, row7960, row7961, row7962, row7963, row7964, row7965, row7966, row7967, row7968, row7969, row7970, row7971, row7972, row7973, row7974, row7975, row7976, row7977, row7978, row7979, row7980]

def rows8_1 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7981, row7982, row7983, row7984, row7985, row7986, row7987, row7988, row7989, row7990, row7991, row7992, row7993, row7994, row7995, row7996, row7997, row7998, row7999, row8000, row8001, row8002, row8003, row8004, row8005, row8006, row8007, row8008, row8009, row8010, row8011, row8012, row8013, row8014, row8015, row8016]

def rows8_2 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8017, row8018, row8019, row8020, row8021, row8022, row8023, row8024, row8025, row8026, row8027, row8028, row8029, row8030, row8031, row8032, row8033, row8034, row8035, row8036, row8037, row8038, row8039, row8040, row8041, row8042, row8043, row8044, row8045, row8046, row8047, row8048, row8049, row8050, row8051, row8052]

end MUB6.Certificate.GramEntries.Block3

end OAI
end


