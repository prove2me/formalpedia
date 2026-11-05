-- Prove2me | Definitions.Def_OAIQ106E074
-- name    : OAIQ106E074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:37:41.132913+00:00
-- url     : https://prove2.me/theorems/adc336b2-ae9c-431e-8dd0-1c2c20aa37cd
-- title:
--   Definitions bundle OAIQ106E074 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedData.sourceChunk10`, `OAI.MUB6.Certificate.MixedData.sourceChunk8`, `OAI.MUB6.Certificate.MixedData.sourceChunk9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Source10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source10.lean), [`MutuallyUnbiased_MixedData_Source8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source8.lean), [`MutuallyUnbiased_MixedData_Source9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source9.lean).
--
--   **Imports.** It imports the bundle `OAIQ106E184` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E077`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E184

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk10 : Array (Integer.Sparse (Fin 3237)) := #[row1280, row1281, row1282, row1283, row1284, row1285, row1286, row1287, row1288, row1289, row1290, row1291, row1292, row1293, row1294, row1295, row1296, row1297, row1298, row1299, row1300, row1301, row1302, row1303, row1304, row1305, row1306, row1307, row1308, row1309, row1310, row1311, row1312, row1313, row1314, row1315, row1316, row1317, row1318, row1319, row1320, row1321, row1322, row1323, row1324, row1325, row1326, row1327, row1328, row1329, row1330, row1331, row1332, row1333, row1334, row1335, row1336, row1337, row1338, row1339, row1340, row1341, row1342, row1343, row1344, row1345, row1346, row1347, row1348, row1349, row1350, row1351, row1352, row1353, row1354, row1355, row1356, row1357, row1358, row1359, row1360, row1361, row1362, row1363, row1364, row1365, row1366, row1367, row1368, row1369, row1370, row1371, row1372, row1373, row1374, row1375, row1376, row1377, row1378, row1379, row1380, row1381, row1382, row1383, row1384, row1385, row1386, row1387, row1388, row1389, row1390, row1391, row1392, row1393, row1394, row1395, row1396, row1397, row1398, row1399, row1400, row1401, row1402, row1403, row1404, row1405, row1406, row1407]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk8 : Array (Integer.Sparse (Fin 3237)) := #[row1024, row1025, row1026, row1027, row1028, row1029, row1030, row1031, row1032, row1033, row1034, row1035, row1036, row1037, row1038, row1039, row1040, row1041, row1042, row1043, row1044, row1045, row1046, row1047, row1048, row1049, row1050, row1051, row1052, row1053, row1054, row1055, row1056, row1057, row1058, row1059, row1060, row1061, row1062, row1063, row1064, row1065, row1066, row1067, row1068, row1069, row1070, row1071, row1072, row1073, row1074, row1075, row1076, row1077, row1078, row1079, row1080, row1081, row1082, row1083, row1084, row1085, row1086, row1087, row1088, row1089, row1090, row1091, row1092, row1093, row1094, row1095, row1096, row1097, row1098, row1099, row1100, row1101, row1102, row1103, row1104, row1105, row1106, row1107, row1108, row1109, row1110, row1111, row1112, row1113, row1114, row1115, row1116, row1117, row1118, row1119, row1120, row1121, row1122, row1123, row1124, row1125, row1126, row1127, row1128, row1129, row1130, row1131, row1132, row1133, row1134, row1135, row1136, row1137, row1138, row1139, row1140, row1141, row1142, row1143, row1144, row1145, row1146, row1147, row1148, row1149, row1150, row1151]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk9 : Array (Integer.Sparse (Fin 3237)) := #[row1152, row1153, row1154, row1155, row1156, row1157, row1158, row1159, row1160, row1161, row1162, row1163, row1164, row1165, row1166, row1167, row1168, row1169, row1170, row1171, row1172, row1173, row1174, row1175, row1176, row1177, row1178, row1179, row1180, row1181, row1182, row1183, row1184, row1185, row1186, row1187, row1188, row1189, row1190, row1191, row1192, row1193, row1194, row1195, row1196, row1197, row1198, row1199, row1200, row1201, row1202, row1203, row1204, row1205, row1206, row1207, row1208, row1209, row1210, row1211, row1212, row1213, row1214, row1215, row1216, row1217, row1218, row1219, row1220, row1221, row1222, row1223, row1224, row1225, row1226, row1227, row1228, row1229, row1230, row1231, row1232, row1233, row1234, row1235, row1236, row1237, row1238, row1239, row1240, row1241, row1242, row1243, row1244, row1245, row1246, row1247, row1248, row1249, row1250, row1251, row1252, row1253, row1254, row1255, row1256, row1257, row1258, row1259, row1260, row1261, row1262, row1263, row1264, row1265, row1266, row1267, row1268, row1269, row1270, row1271, row1272, row1273, row1274, row1275, row1276, row1277, row1278, row1279]

end MUB6.Certificate.MixedData

end OAI
end


