-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice03_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice03_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:16.816743+00:00
-- url     : https://prove2.me/theorems/04816592-851a-4987-b058-087a1c5afcb9
-- title:
--   Exact Pell certificate records 193–256
-- statement:
--   The exact consecutive certificate records 193 through 256 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_004
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_005

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice03_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨1871,pellFiniteCertificate_1871⟩,
   ⟨1879,pellFiniteCertificate_1879⟩,
   ⟨1887,pellFiniteCertificate_1887⟩,
   ⟨1895,pellFiniteCertificate_1895⟩,
   ⟨1903,pellFiniteCertificate_1903⟩,
   ⟨1919,pellFiniteCertificate_1919⟩,
   ⟨1927,pellFiniteCertificate_1927⟩,
   ⟨1943,pellFiniteCertificate_1943⟩,
   ⟨1951,pellFiniteCertificate_1951⟩,
   ⟨1959,pellFiniteCertificate_1959⟩,
   ⟨1967,pellFiniteCertificate_1967⟩,
   ⟨1983,pellFiniteCertificate_1983⟩,
   ⟨1991,pellFiniteCertificate_1991⟩,
   ⟨1999,pellFiniteCertificate_1999⟩,
   ⟨2015,pellFiniteCertificate_2015⟩,
   ⟨2031,pellFiniteCertificate_2031⟩,
   ⟨2039,pellFiniteCertificate_2039⟩,
   ⟨2047,pellFiniteCertificate_2047⟩,
   ⟨2055,pellFiniteCertificate_2055⟩,
   ⟨2063,pellFiniteCertificate_2063⟩,
   ⟨2071,pellFiniteCertificate_2071⟩,
   ⟨2087,pellFiniteCertificate_2087⟩,
   ⟨2095,pellFiniteCertificate_2095⟩,
   ⟨2103,pellFiniteCertificate_2103⟩,
   ⟨2111,pellFiniteCertificate_2111⟩,
   ⟨2119,pellFiniteCertificate_2119⟩,
   ⟨2127,pellFiniteCertificate_2127⟩,
   ⟨2135,pellFiniteCertificate_2135⟩,
   ⟨2143,pellFiniteCertificate_2143⟩,
   ⟨2159,pellFiniteCertificate_2159⟩,
   ⟨2167,pellFiniteCertificate_2167⟩,
   ⟨2183,pellFiniteCertificate_2183⟩,
   ⟨2191,pellFiniteCertificate_2191⟩,
   ⟨2199,pellFiniteCertificate_2199⟩,
   ⟨2207,pellFiniteCertificate_2207⟩,
   ⟨2215,pellFiniteCertificate_2215⟩,
   ⟨2231,pellFiniteCertificate_2231⟩,
   ⟨2239,pellFiniteCertificate_2239⟩,
   ⟨2247,pellFiniteCertificate_2247⟩,
   ⟨2255,pellFiniteCertificate_2255⟩,
   ⟨2263,pellFiniteCertificate_2263⟩,
   ⟨2271,pellFiniteCertificate_2271⟩,
   ⟨2279,pellFiniteCertificate_2279⟩,
   ⟨2287,pellFiniteCertificate_2287⟩,
   ⟨2311,pellFiniteCertificate_2311⟩,
   ⟨2319,pellFiniteCertificate_2319⟩,
   ⟨2327,pellFiniteCertificate_2327⟩,
   ⟨2335,pellFiniteCertificate_2335⟩,
   ⟨2343,pellFiniteCertificate_2343⟩,
   ⟨2351,pellFiniteCertificate_2351⟩,
   ⟨2359,pellFiniteCertificate_2359⟩,
   ⟨2383,pellFiniteCertificate_2383⟩,
   ⟨2391,pellFiniteCertificate_2391⟩,
   ⟨2399,pellFiniteCertificate_2399⟩,
   ⟨2407,pellFiniteCertificate_2407⟩,
   ⟨2415,pellFiniteCertificate_2415⟩,
   ⟨2423,pellFiniteCertificate_2423⟩,
   ⟨2431,pellFiniteCertificate_2431⟩,
   ⟨2447,pellFiniteCertificate_2447⟩,
   ⟨2455,pellFiniteCertificate_2455⟩,
   ⟨2463,pellFiniteCertificate_2463⟩,
   ⟨2471,pellFiniteCertificate_2471⟩,
   ⟨2479,pellFiniteCertificate_2479⟩,
   ⟨2487,pellFiniteCertificate_2487⟩]

end D1Bound5


