-- Prove2me | Definitions.Def_OAIQ106E073
-- name    : OAIQ106E073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:34:44.40245+00:00
-- url     : https://prove2.me/theorems/4fce995f-772e-4c0d-8ee0-cc5fe1df7f21
-- title:
--   Definitions bundle OAIQ106E073 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedData.sourceChunk1`, `OAI.MUB6.Certificate.MixedData.sourceChunk11`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Source1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source1.lean), [`MutuallyUnbiased_MixedData_Source11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source11.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E184` and `OAIQ106E070` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E077`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E070

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk1 : Array (Integer.Sparse (Fin 3237)) := #[row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167, row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209, row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251, row252, row253, row254, row255]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk11 : Array (Integer.Sparse (Fin 3237)) := #[row1408, row1409, row1410, row1411, row1412, row1413, row1414, row1415, row1416, row1417, row1418, row1419, row1420, row1421, row1422, row1423, row1424, row1425, row1426, row1427, row1428, row1429, row1430, row1431, row1432, row1433, row1434, row1435, row1436, row1437, row1438, row1439, row1440, row1441, row1442, row1443, row1444, row1445, row1446, row1447, row1448, row1449, row1450, row1451, row1452, row1453, row1454, row1455, row1456, row1457, row1458, row1459, row1460, row1461, row1462, row1463, row1464, row1465, row1466, row1467, row1468, row1469, row1470, row1471, row1472, row1473, row1474, row1475, row1476, row1477, row1478, row1479, row1480, row1481, row1482, row1483, row1484, row1485, row1486, row1487, row1488, row1489, row1490, row1491, row1492, row1493, row1494, row1495, row1496, row1497, row1498, row1499, row1500, row1501, row1502, row1503, row1504, row1505, row1506, row1507, row1508, row1509, row1510, row1511, row1512, row1513, row1514, row1515, row1516, row1517, row1518, row1519, row1520, row1521, row1522, row1523, row1524, row1525, row1526, row1527, row1528, row1529, row1530, row1531, row1532, row1533, row1534, row1535]

end MUB6.Certificate.MixedData

end OAI
end


