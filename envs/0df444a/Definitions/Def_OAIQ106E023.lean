-- Prove2me | Definitions.Def_OAIQ106E023
-- name    : OAIQ106E023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:38:14.838295+00:00
-- url     : https://prove2.me/theorems/4340ebb6-a7b6-4ae3-aef1-313bfca702b2
-- title:
--   Definitions bundle OAIQ106E023 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 48 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows7_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows8_8`, `OAI.MUB6.Certificate.GramEntries.Block2.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_10`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_4`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_5`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_6`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_7`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_8`, `OAI.MUB6.Certificate.GramEntries.Block2.rows10_9`, `OAI.MUB6.Certificate.GramEntries.Block2.rows1_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows1_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows2_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows4_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows4_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows4_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows4_3`, `OAI.MUB6.Certificate.GramEntries.Block2.rows4_4`, `OAI.MUB6.Certificate.GramEntries.Block2.rows5_0`, `OAI.MUB6.Certificate.GramEntries.Block2.rows5_1`, `OAI.MUB6.Certificate.GramEntries.Block2.rows5_2`, `OAI.MUB6.Certificate.GramEntries.Block2.rows5_3` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block1Row7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row7.lean), [`MutuallyUnbiased_GramEntries_Block1Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row8.lean), [`MutuallyUnbiased_GramEntries_Block2Row0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row0.lean), [`MutuallyUnbiased_GramEntries_Block2Row1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row1.lean), [`MutuallyUnbiased_GramEntries_Block2Row10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row10.lean), [`MutuallyUnbiased_GramEntries_Block2Row2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row2.lean), [`MutuallyUnbiased_GramEntries_Block2Row3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row3.lean), [`MutuallyUnbiased_GramEntries_Block2Row4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row4.lean), [`MutuallyUnbiased_GramEntries_Block2Row5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row5.lean), [`MutuallyUnbiased_GramEntries_Block2Row6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row6.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018` and `OAIQ106E021` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval0_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_7_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval1_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval2_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval3_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval3_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_0_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval6_4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6_e` and `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E021

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_7 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1320, row1321, row1322, row1323, row1324, row1325, row1326, row1327, row1328, row1329, row1330, row1331, row1332, row1333, row1334, row1335, row1336, row1337, row1338, row1339, row1340, row1341, row1342, row1343, row1344, row1345, row1346, row1347, row1348, row1349]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1350, row1351, row1352, row1353, row1354, row1355, row1356, row1357, row1358, row1359, row1360, row1361, row1362, row1363]

def rows8_1 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1364, row1365, row1366, row1367, row1368, row1369, row1370, row1371, row1372, row1373, row1374, row1375, row1376, row1377]

def rows8_2 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1378, row1379, row1380, row1381, row1382, row1383, row1384, row1385, row1386, row1387, row1388, row1389, row1390, row1391]

def rows8_3 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1392, row1393, row1394, row1395, row1396, row1397, row1398, row1399, row1400, row1401, row1402, row1403, row1404, row1405]

def rows8_4 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1406, row1407, row1408, row1409, row1410, row1411, row1412, row1413, row1414, row1415, row1416, row1417, row1418, row1419]

def rows8_5 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1420, row1421, row1422, row1423, row1424, row1425, row1426, row1427, row1428, row1429, row1430, row1431, row1432, row1433]

def rows8_6 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1434, row1435, row1436, row1437, row1438, row1439, row1440, row1441, row1442, row1443, row1444, row1445, row1446, row1447]

def rows8_7 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1448, row1449, row1450, row1451, row1452, row1453, row1454, row1455, row1456, row1457, row1458, row1459, row1460, row1461]

def rows8_8 : Fin GramFunctions.Block1.form8.size → Integer.Sparse Key := ![row1462, row1463, row1464, row1465, row1466, row1467, row1468, row1469, row1470, row1471, row1472, row1473, row1474, row1475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block2.form0.size → Integer.Sparse Key := ![row5148, row5149, row5150, row5151, row5152, row5153, row5154, row5155, row5156, row5157, row5158, row5159, row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row5172, row5173, row5174, row5175, row5176, row5177, row5178, row5179, row5180, row5181, row5182, row5183, row5184, row5185, row5186, row5187]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5188, row5189, row5190, row5191, row5192, row5193, row5194, row5195, row5196, row5197, row5198, row5199, row5200, row5201, row5202, row5203, row5204, row5205, row5206, row5207, row5208, row5209, row5210, row5211, row5212, row5213, row5214, row5215, row5216, row5217, row5218, row5219, row5220, row5221, row5222, row5223, row5224, row5225, row5226, row5227]

def rows1_1 : Fin GramFunctions.Block2.form1.size → Integer.Sparse Key := ![row5228, row5229, row5230, row5231, row5232, row5233, row5234, row5235, row5236, row5237, row5238, row5239, row5240, row5241, row5242, row5243, row5244, row5245, row5246, row5247, row5248, row5249, row5250, row5251, row5252, row5253, row5254, row5255, row5256, row5257, row5258, row5259, row5260, row5261, row5262, row5263, row5264, row5265, row5266, row5267]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7018, row7019, row7020, row7021, row7022, row7023, row7024, row7025, row7026, row7027, row7028, row7029, row7030, row7031, row7032, row7033, row7034, row7035, row7036, row7037, row7038, row7039, row7040, row7041, row7042, row7043, row7044, row7045, row7046, row7047]

def rows10_1 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7048, row7049, row7050, row7051, row7052, row7053, row7054, row7055, row7056, row7057, row7058, row7059, row7060, row7061, row7062, row7063, row7064, row7065, row7066, row7067, row7068, row7069, row7070, row7071, row7072, row7073, row7074, row7075, row7076, row7077]

def rows10_2 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7078, row7079, row7080, row7081, row7082, row7083, row7084, row7085, row7086, row7087, row7088, row7089, row7090, row7091, row7092, row7093, row7094, row7095, row7096, row7097, row7098, row7099, row7100, row7101, row7102, row7103, row7104, row7105, row7106, row7107]

def rows10_3 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7108, row7109, row7110, row7111, row7112, row7113, row7114, row7115, row7116, row7117, row7118, row7119, row7120, row7121, row7122, row7123, row7124, row7125, row7126, row7127, row7128, row7129, row7130, row7131, row7132, row7133, row7134, row7135, row7136, row7137]

def rows10_4 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7138, row7139, row7140, row7141, row7142, row7143, row7144, row7145, row7146, row7147, row7148, row7149, row7150, row7151, row7152, row7153, row7154, row7155, row7156, row7157, row7158, row7159, row7160, row7161, row7162, row7163, row7164, row7165, row7166, row7167]

def rows10_5 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7168, row7169, row7170, row7171, row7172, row7173, row7174, row7175, row7176, row7177, row7178, row7179, row7180, row7181, row7182, row7183, row7184, row7185, row7186, row7187, row7188, row7189, row7190, row7191, row7192, row7193, row7194, row7195, row7196, row7197]

def rows10_6 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7198, row7199, row7200, row7201, row7202, row7203, row7204, row7205, row7206, row7207, row7208, row7209, row7210, row7211, row7212, row7213, row7214, row7215, row7216, row7217, row7218, row7219, row7220, row7221, row7222, row7223, row7224, row7225, row7226, row7227]

def rows10_7 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7228, row7229, row7230, row7231, row7232, row7233, row7234, row7235, row7236, row7237, row7238, row7239, row7240, row7241, row7242, row7243, row7244, row7245, row7246, row7247, row7248, row7249, row7250, row7251, row7252, row7253, row7254, row7255, row7256, row7257]

def rows10_8 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7258, row7259, row7260, row7261, row7262, row7263, row7264, row7265, row7266, row7267, row7268, row7269, row7270, row7271, row7272, row7273, row7274, row7275, row7276, row7277, row7278, row7279, row7280, row7281, row7282, row7283, row7284, row7285, row7286, row7287]

def rows10_9 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7288, row7289, row7290, row7291, row7292, row7293, row7294, row7295, row7296, row7297, row7298, row7299, row7300, row7301, row7302, row7303, row7304, row7305, row7306, row7307, row7308, row7309, row7310, row7311, row7312, row7313, row7314, row7315, row7316, row7317]

def rows10_10 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7318, row7319, row7320, row7321, row7322, row7323, row7324, row7325, row7326, row7327, row7328, row7329, row7330, row7331, row7332, row7333, row7334, row7335, row7336, row7337, row7338, row7339, row7340, row7341, row7342, row7343, row7344, row7345, row7346, row7347]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5268, row5269, row5270, row5271, row5272, row5273, row5274, row5275, row5276, row5277, row5278, row5279, row5280, row5281, row5282, row5283, row5284, row5285, row5286, row5287, row5288, row5289, row5290, row5291, row5292, row5293, row5294, row5295, row5296, row5297, row5298, row5299, row5300, row5301, row5302, row5303, row5304, row5305, row5306, row5307]

def rows2_1 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5308, row5309, row5310, row5311, row5312, row5313, row5314, row5315, row5316, row5317, row5318, row5319, row5320, row5321, row5322, row5323, row5324, row5325, row5326, row5327, row5328, row5329, row5330, row5331, row5332, row5333, row5334, row5335, row5336, row5337, row5338, row5339, row5340, row5341, row5342, row5343, row5344, row5345, row5346, row5347]

def rows2_2 : Fin GramFunctions.Block2.form2.size → Integer.Sparse Key := ![row5348, row5349, row5350, row5351, row5352, row5353, row5354, row5355, row5356, row5357, row5358, row5359, row5360, row5361, row5362, row5363, row5364, row5365, row5366, row5367, row5368, row5369, row5370, row5371, row5372, row5373, row5374, row5375, row5376, row5377, row5378, row5379, row5380, row5381, row5382, row5383, row5384, row5385, row5386, row5387]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5388, row5389, row5390, row5391, row5392, row5393, row5394, row5395, row5396, row5397, row5398, row5399, row5400, row5401, row5402, row5403, row5404, row5405, row5406, row5407, row5408, row5409, row5410, row5411, row5412, row5413, row5414, row5415, row5416, row5417]

def rows3_1 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5418, row5419, row5420, row5421, row5422, row5423, row5424, row5425, row5426, row5427, row5428, row5429, row5430, row5431, row5432, row5433, row5434, row5435, row5436, row5437, row5438, row5439, row5440, row5441, row5442, row5443, row5444, row5445, row5446, row5447]

def rows3_2 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5448, row5449, row5450, row5451, row5452, row5453, row5454, row5455, row5456, row5457, row5458, row5459, row5460, row5461, row5462, row5463, row5464, row5465, row5466, row5467, row5468, row5469, row5470, row5471, row5472, row5473, row5474, row5475, row5476, row5477]

def rows3_3 : Fin GramFunctions.Block2.form3.size → Integer.Sparse Key := ![row5478, row5479, row5480, row5481, row5482, row5483, row5484, row5485, row5486, row5487, row5488, row5489, row5490, row5491, row5492, row5493, row5494, row5495, row5496, row5497, row5498, row5499, row5500, row5501, row5502, row5503, row5504, row5505, row5506, row5507]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5508, row5509, row5510, row5511, row5512, row5513, row5514, row5515, row5516, row5517, row5518, row5519, row5520, row5521, row5522, row5523, row5524, row5525, row5526, row5527, row5528, row5529, row5530, row5531, row5532, row5533, row5534, row5535, row5536, row5537]

def rows4_1 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5538, row5539, row5540, row5541, row5542, row5543, row5544, row5545, row5546, row5547, row5548, row5549, row5550, row5551, row5552, row5553, row5554, row5555, row5556, row5557, row5558, row5559, row5560, row5561, row5562, row5563, row5564, row5565, row5566, row5567]

def rows4_2 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5568, row5569, row5570, row5571, row5572, row5573, row5574, row5575, row5576, row5577, row5578, row5579, row5580, row5581, row5582, row5583, row5584, row5585, row5586, row5587, row5588, row5589, row5590, row5591, row5592, row5593, row5594, row5595, row5596, row5597]

def rows4_3 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5598, row5599, row5600, row5601, row5602, row5603, row5604, row5605, row5606, row5607, row5608, row5609, row5610, row5611, row5612, row5613, row5614, row5615, row5616, row5617, row5618, row5619, row5620, row5621, row5622, row5623, row5624, row5625, row5626, row5627]

def rows4_4 : Fin GramFunctions.Block2.form4.size → Integer.Sparse Key := ![row5628, row5629, row5630, row5631, row5632, row5633, row5634, row5635, row5636, row5637, row5638, row5639, row5640, row5641, row5642, row5643, row5644, row5645, row5646, row5647, row5648, row5649, row5650, row5651, row5652, row5653, row5654, row5655, row5656, row5657]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5658, row5659, row5660, row5661, row5662, row5663, row5664, row5665, row5666, row5667, row5668, row5669, row5670, row5671, row5672, row5673, row5674, row5675, row5676, row5677, row5678, row5679, row5680, row5681, row5682, row5683, row5684, row5685, row5686, row5687, row5688, row5689, row5690, row5691, row5692, row5693, row5694, row5695, row5696, row5697]

def rows5_1 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5698, row5699, row5700, row5701, row5702, row5703, row5704, row5705, row5706, row5707, row5708, row5709, row5710, row5711, row5712, row5713, row5714, row5715, row5716, row5717, row5718, row5719, row5720, row5721, row5722, row5723, row5724, row5725, row5726, row5727, row5728, row5729, row5730, row5731, row5732, row5733, row5734, row5735, row5736, row5737]

def rows5_2 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5738, row5739, row5740, row5741, row5742, row5743, row5744, row5745, row5746, row5747, row5748, row5749, row5750, row5751, row5752, row5753, row5754, row5755, row5756, row5757, row5758, row5759, row5760, row5761, row5762, row5763, row5764, row5765, row5766, row5767, row5768, row5769, row5770, row5771, row5772, row5773, row5774, row5775, row5776, row5777]

def rows5_3 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5778, row5779, row5780, row5781, row5782, row5783, row5784, row5785, row5786, row5787, row5788, row5789, row5790, row5791, row5792, row5793, row5794, row5795, row5796, row5797, row5798, row5799, row5800, row5801, row5802, row5803, row5804, row5805, row5806, row5807, row5808, row5809, row5810, row5811, row5812, row5813, row5814, row5815, row5816, row5817]

def rows5_4 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5818, row5819, row5820, row5821, row5822, row5823, row5824, row5825, row5826, row5827, row5828, row5829, row5830, row5831, row5832, row5833, row5834, row5835, row5836, row5837, row5838, row5839, row5840, row5841, row5842, row5843, row5844, row5845, row5846, row5847, row5848, row5849, row5850, row5851, row5852, row5853, row5854, row5855, row5856, row5857]

def rows5_5 : Fin GramFunctions.Block2.form5.size → Integer.Sparse Key := ![row5858, row5859, row5860, row5861, row5862, row5863, row5864, row5865, row5866, row5867, row5868, row5869, row5870, row5871, row5872, row5873, row5874, row5875, row5876, row5877, row5878, row5879, row5880, row5881, row5882, row5883, row5884, row5885, row5886, row5887, row5888, row5889, row5890, row5891, row5892, row5893, row5894, row5895, row5896, row5897]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

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

def rows6_0 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5898, row5899, row5900, row5901, row5902, row5903, row5904, row5905, row5906, row5907, row5908, row5909, row5910, row5911, row5912, row5913, row5914, row5915, row5916, row5917, row5918, row5919, row5920, row5921, row5922, row5923, row5924, row5925, row5926, row5927, row5928, row5929, row5930, row5931, row5932, row5933, row5934, row5935, row5936, row5937]

def rows6_1 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5938, row5939, row5940, row5941, row5942, row5943, row5944, row5945, row5946, row5947, row5948, row5949, row5950, row5951, row5952, row5953, row5954, row5955, row5956, row5957, row5958, row5959, row5960, row5961, row5962, row5963, row5964, row5965, row5966, row5967, row5968, row5969, row5970, row5971, row5972, row5973, row5974, row5975, row5976, row5977]

def rows6_2 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row5978, row5979, row5980, row5981, row5982, row5983, row5984, row5985, row5986, row5987, row5988, row5989, row5990, row5991, row5992, row5993, row5994, row5995, row5996, row5997, row5998, row5999, row6000, row6001, row6002, row6003, row6004, row6005, row6006, row6007, row6008, row6009, row6010, row6011, row6012, row6013, row6014, row6015, row6016, row6017]

def rows6_3 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6018, row6019, row6020, row6021, row6022, row6023, row6024, row6025, row6026, row6027, row6028, row6029, row6030, row6031, row6032, row6033, row6034, row6035, row6036, row6037, row6038, row6039, row6040, row6041, row6042, row6043, row6044, row6045, row6046, row6047, row6048, row6049, row6050, row6051, row6052, row6053, row6054, row6055, row6056, row6057]

def rows6_4 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6058, row6059, row6060, row6061, row6062, row6063, row6064, row6065, row6066, row6067, row6068, row6069, row6070, row6071, row6072, row6073, row6074, row6075, row6076, row6077, row6078, row6079, row6080, row6081, row6082, row6083, row6084, row6085, row6086, row6087, row6088, row6089, row6090, row6091, row6092, row6093, row6094, row6095, row6096, row6097]

def rows6_5 : Fin GramFunctions.Block2.form6.size → Integer.Sparse Key := ![row6098, row6099, row6100, row6101, row6102, row6103, row6104, row6105, row6106, row6107, row6108, row6109, row6110, row6111, row6112, row6113, row6114, row6115, row6116, row6117, row6118, row6119, row6120, row6121, row6122, row6123, row6124, row6125, row6126, row6127, row6128, row6129, row6130, row6131, row6132, row6133, row6134, row6135, row6136, row6137]

end MUB6.Certificate.GramEntries.Block2

end OAI
end


