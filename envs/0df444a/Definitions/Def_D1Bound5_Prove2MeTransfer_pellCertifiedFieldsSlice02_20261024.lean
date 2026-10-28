-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice02_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice02_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:18:16.370547+00:00
-- url     : https://prove2.me/theorems/015c1f70-67dc-437a-b9c3-6344e1ab08e2
-- title:
--   Exact Pell certificate records 129–192
-- statement:
--   The exact consecutive certificate records 129 through 192 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_003
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_004

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice02_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨1255,pellFiniteCertificate_1255⟩,
   ⟨1263,pellFiniteCertificate_1263⟩,
   ⟨1271,pellFiniteCertificate_1271⟩,
   ⟨1279,pellFiniteCertificate_1279⟩,
   ⟨1295,pellFiniteCertificate_1295⟩,
   ⟨1303,pellFiniteCertificate_1303⟩,
   ⟨1311,pellFiniteCertificate_1311⟩,
   ⟨1319,pellFiniteCertificate_1319⟩,
   ⟨1327,pellFiniteCertificate_1327⟩,
   ⟨1335,pellFiniteCertificate_1335⟩,
   ⟨1343,pellFiniteCertificate_1343⟩,
   ⟨1351,pellFiniteCertificate_1351⟩,
   ⟨1367,pellFiniteCertificate_1367⟩,
   ⟨1383,pellFiniteCertificate_1383⟩,
   ⟨1391,pellFiniteCertificate_1391⟩,
   ⟨1399,pellFiniteCertificate_1399⟩,
   ⟨1407,pellFiniteCertificate_1407⟩,
   ⟨1415,pellFiniteCertificate_1415⟩,
   ⟨1423,pellFiniteCertificate_1423⟩,
   ⟨1439,pellFiniteCertificate_1439⟩,
   ⟨1447,pellFiniteCertificate_1447⟩,
   ⟨1455,pellFiniteCertificate_1455⟩,
   ⟨1463,pellFiniteCertificate_1463⟩,
   ⟨1471,pellFiniteCertificate_1471⟩,
   ⟨1479,pellFiniteCertificate_1479⟩,
   ⟨1487,pellFiniteCertificate_1487⟩,
   ⟨1495,pellFiniteCertificate_1495⟩,
   ⟨1511,pellFiniteCertificate_1511⟩,
   ⟨1527,pellFiniteCertificate_1527⟩,
   ⟨1535,pellFiniteCertificate_1535⟩,
   ⟨1543,pellFiniteCertificate_1543⟩,
   ⟨1551,pellFiniteCertificate_1551⟩,
   ⟨1559,pellFiniteCertificate_1559⟩,
   ⟨1567,pellFiniteCertificate_1567⟩,
   ⟨1583,pellFiniteCertificate_1583⟩,
   ⟨1591,pellFiniteCertificate_1591⟩,
   ⟨1599,pellFiniteCertificate_1599⟩,
   ⟨1607,pellFiniteCertificate_1607⟩,
   ⟨1615,pellFiniteCertificate_1615⟩,
   ⟨1623,pellFiniteCertificate_1623⟩,
   ⟨1631,pellFiniteCertificate_1631⟩,
   ⟨1639,pellFiniteCertificate_1639⟩,
   ⟨1655,pellFiniteCertificate_1655⟩,
   ⟨1663,pellFiniteCertificate_1663⟩,
   ⟨1671,pellFiniteCertificate_1671⟩,
   ⟨1679,pellFiniteCertificate_1679⟩,
   ⟨1687,pellFiniteCertificate_1687⟩,
   ⟨1695,pellFiniteCertificate_1695⟩,
   ⟨1703,pellFiniteCertificate_1703⟩,
   ⟨1711,pellFiniteCertificate_1711⟩,
   ⟨1727,pellFiniteCertificate_1727⟩,
   ⟨1735,pellFiniteCertificate_1735⟩,
   ⟨1743,pellFiniteCertificate_1743⟩,
   ⟨1751,pellFiniteCertificate_1751⟩,
   ⟨1759,pellFiniteCertificate_1759⟩,
   ⟨1767,pellFiniteCertificate_1767⟩,
   ⟨1783,pellFiniteCertificate_1783⟩,
   ⟨1799,pellFiniteCertificate_1799⟩,
   ⟨1807,pellFiniteCertificate_1807⟩,
   ⟨1823,pellFiniteCertificate_1823⟩,
   ⟨1831,pellFiniteCertificate_1831⟩,
   ⟨1839,pellFiniteCertificate_1839⟩,
   ⟨1847,pellFiniteCertificate_1847⟩,
   ⟨1855,pellFiniteCertificate_1855⟩]

end D1Bound5


