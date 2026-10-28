-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice08_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice08_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:34.783863+00:00
-- url     : https://prove2.me/theorems/36b0f4d3-37c4-4871-99db-47b7be76f97e
-- title:
--   Exact Pell certificate records 513–576
-- statement:
--   The exact consecutive certificate records 513 through 576 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_009

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice08_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨5023,pellFiniteCertificate_5023⟩,
   ⟨5039,pellFiniteCertificate_5039⟩,
   ⟨5055,pellFiniteCertificate_5055⟩,
   ⟨5063,pellFiniteCertificate_5063⟩,
   ⟨5071,pellFiniteCertificate_5071⟩,
   ⟨5079,pellFiniteCertificate_5079⟩,
   ⟨5087,pellFiniteCertificate_5087⟩,
   ⟨5095,pellFiniteCertificate_5095⟩,
   ⟨5111,pellFiniteCertificate_5111⟩,
   ⟨5119,pellFiniteCertificate_5119⟩,
   ⟨5127,pellFiniteCertificate_5127⟩,
   ⟨5135,pellFiniteCertificate_5135⟩,
   ⟨5143,pellFiniteCertificate_5143⟩,
   ⟨5151,pellFiniteCertificate_5151⟩,
   ⟨5159,pellFiniteCertificate_5159⟩,
   ⟨5167,pellFiniteCertificate_5167⟩,
   ⟨5183,pellFiniteCertificate_5183⟩,
   ⟨5191,pellFiniteCertificate_5191⟩,
   ⟨5199,pellFiniteCertificate_5199⟩,
   ⟨5207,pellFiniteCertificate_5207⟩,
   ⟨5215,pellFiniteCertificate_5215⟩,
   ⟨5223,pellFiniteCertificate_5223⟩,
   ⟨5231,pellFiniteCertificate_5231⟩,
   ⟨5255,pellFiniteCertificate_5255⟩,
   ⟨5263,pellFiniteCertificate_5263⟩,
   ⟨5271,pellFiniteCertificate_5271⟩,
   ⟨5279,pellFiniteCertificate_5279⟩,
   ⟨5287,pellFiniteCertificate_5287⟩,
   ⟨5295,pellFiniteCertificate_5295⟩,
   ⟨5303,pellFiniteCertificate_5303⟩,
   ⟨5311,pellFiniteCertificate_5311⟩,
   ⟨5327,pellFiniteCertificate_5327⟩,
   ⟨5335,pellFiniteCertificate_5335⟩,
   ⟨5343,pellFiniteCertificate_5343⟩,
   ⟨5351,pellFiniteCertificate_5351⟩,
   ⟨5359,pellFiniteCertificate_5359⟩,
   ⟨5367,pellFiniteCertificate_5367⟩,
   ⟨5383,pellFiniteCertificate_5383⟩,
   ⟨5399,pellFiniteCertificate_5399⟩,
   ⟨5407,pellFiniteCertificate_5407⟩,
   ⟨5423,pellFiniteCertificate_5423⟩,
   ⟨5431,pellFiniteCertificate_5431⟩,
   ⟨5447,pellFiniteCertificate_5447⟩,
   ⟨5455,pellFiniteCertificate_5455⟩,
   ⟨5471,pellFiniteCertificate_5471⟩,
   ⟨5479,pellFiniteCertificate_5479⟩,
   ⟨5487,pellFiniteCertificate_5487⟩,
   ⟨5495,pellFiniteCertificate_5495⟩,
   ⟨5503,pellFiniteCertificate_5503⟩,
   ⟨5511,pellFiniteCertificate_5511⟩,
   ⟨5519,pellFiniteCertificate_5519⟩,
   ⟨5527,pellFiniteCertificate_5527⟩,
   ⟨5543,pellFiniteCertificate_5543⟩,
   ⟨5551,pellFiniteCertificate_5551⟩,
   ⟨5559,pellFiniteCertificate_5559⟩,
   ⟨5567,pellFiniteCertificate_5567⟩,
   ⟨5583,pellFiniteCertificate_5583⟩,
   ⟨5591,pellFiniteCertificate_5591⟩,
   ⟨5599,pellFiniteCertificate_5599⟩,
   ⟨5615,pellFiniteCertificate_5615⟩,
   ⟨5623,pellFiniteCertificate_5623⟩,
   ⟨5631,pellFiniteCertificate_5631⟩,
   ⟨5639,pellFiniteCertificate_5639⟩,
   ⟨5647,pellFiniteCertificate_5647⟩]

end D1Bound5


