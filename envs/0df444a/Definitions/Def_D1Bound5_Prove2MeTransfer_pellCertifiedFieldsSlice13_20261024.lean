-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice13_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice13_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:16:13.189473+00:00
-- url     : https://prove2.me/theorems/0c87fa08-b563-4f6f-94c1-eb38c3db5334
-- title:
--   Exact Pell certificate records 833–896
-- statement:
--   The exact consecutive certificate records 833 through 896 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_014

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice13_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨8191,pellFiniteCertificate_8191⟩,
   ⟨8207,pellFiniteCertificate_8207⟩,
   ⟨8215,pellFiniteCertificate_8215⟩,
   ⟨8223,pellFiniteCertificate_8223⟩,
   ⟨8231,pellFiniteCertificate_8231⟩,
   ⟨8239,pellFiniteCertificate_8239⟩,
   ⟨8247,pellFiniteCertificate_8247⟩,
   ⟨8255,pellFiniteCertificate_8255⟩,
   ⟨8263,pellFiniteCertificate_8263⟩,
   ⟨8279,pellFiniteCertificate_8279⟩,
   ⟨8287,pellFiniteCertificate_8287⟩,
   ⟨8295,pellFiniteCertificate_8295⟩,
   ⟨8311,pellFiniteCertificate_8311⟩,
   ⟨8319,pellFiniteCertificate_8319⟩,
   ⟨8327,pellFiniteCertificate_8327⟩,
   ⟨8335,pellFiniteCertificate_8335⟩,
   ⟨8351,pellFiniteCertificate_8351⟩,
   ⟨8359,pellFiniteCertificate_8359⟩,
   ⟨8367,pellFiniteCertificate_8367⟩,
   ⟨8383,pellFiniteCertificate_8383⟩,
   ⟨8391,pellFiniteCertificate_8391⟩,
   ⟨8399,pellFiniteCertificate_8399⟩,
   ⟨8407,pellFiniteCertificate_8407⟩,
   ⟨8423,pellFiniteCertificate_8423⟩,
   ⟨8431,pellFiniteCertificate_8431⟩,
   ⟨8439,pellFiniteCertificate_8439⟩,
   ⟨8447,pellFiniteCertificate_8447⟩,
   ⟨8455,pellFiniteCertificate_8455⟩,
   ⟨8463,pellFiniteCertificate_8463⟩,
   ⟨8471,pellFiniteCertificate_8471⟩,
   ⟨8479,pellFiniteCertificate_8479⟩,
   ⟨8495,pellFiniteCertificate_8495⟩,
   ⟨8503,pellFiniteCertificate_8503⟩,
   ⟨8511,pellFiniteCertificate_8511⟩,
   ⟨8519,pellFiniteCertificate_8519⟩,
   ⟨8527,pellFiniteCertificate_8527⟩,
   ⟨8535,pellFiniteCertificate_8535⟩,
   ⟨8543,pellFiniteCertificate_8543⟩,
   ⟨8551,pellFiniteCertificate_8551⟩,
   ⟨8567,pellFiniteCertificate_8567⟩,
   ⟨8583,pellFiniteCertificate_8583⟩,
   ⟨8599,pellFiniteCertificate_8599⟩,
   ⟨8607,pellFiniteCertificate_8607⟩,
   ⟨8615,pellFiniteCertificate_8615⟩,
   ⟨8623,pellFiniteCertificate_8623⟩,
   ⟨8639,pellFiniteCertificate_8639⟩,
   ⟨8647,pellFiniteCertificate_8647⟩,
   ⟨8655,pellFiniteCertificate_8655⟩,
   ⟨8663,pellFiniteCertificate_8663⟩,
   ⟨8671,pellFiniteCertificate_8671⟩,
   ⟨8679,pellFiniteCertificate_8679⟩,
   ⟨8687,pellFiniteCertificate_8687⟩,
   ⟨8695,pellFiniteCertificate_8695⟩,
   ⟨8711,pellFiniteCertificate_8711⟩,
   ⟨8719,pellFiniteCertificate_8719⟩,
   ⟨8727,pellFiniteCertificate_8727⟩,
   ⟨8735,pellFiniteCertificate_8735⟩,
   ⟨8743,pellFiniteCertificate_8743⟩,
   ⟨8751,pellFiniteCertificate_8751⟩,
   ⟨8759,pellFiniteCertificate_8759⟩,
   ⟨8767,pellFiniteCertificate_8767⟩,
   ⟨8783,pellFiniteCertificate_8783⟩,
   ⟨8791,pellFiniteCertificate_8791⟩,
   ⟨8799,pellFiniteCertificate_8799⟩]

end D1Bound5


