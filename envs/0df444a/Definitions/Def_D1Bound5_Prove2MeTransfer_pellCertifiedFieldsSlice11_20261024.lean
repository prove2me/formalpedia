-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice11_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice11_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:18:34.911005+00:00
-- url     : https://prove2.me/theorems/a2d00d67-0716-4031-9801-e81d06058d7b
-- title:
--   Exact Pell certificate records 705–768
-- statement:
--   The exact consecutive certificate records 705 through 768 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_012

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice11_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨6935,pellFiniteCertificate_6935⟩,
   ⟨6943,pellFiniteCertificate_6943⟩,
   ⟨6951,pellFiniteCertificate_6951⟩,
   ⟨6959,pellFiniteCertificate_6959⟩,
   ⟨6967,pellFiniteCertificate_6967⟩,
   ⟨6983,pellFiniteCertificate_6983⟩,
   ⟨6991,pellFiniteCertificate_6991⟩,
   ⟨6999,pellFiniteCertificate_6999⟩,
   ⟨7015,pellFiniteCertificate_7015⟩,
   ⟨7023,pellFiniteCertificate_7023⟩,
   ⟨7031,pellFiniteCertificate_7031⟩,
   ⟨7039,pellFiniteCertificate_7039⟩,
   ⟨7055,pellFiniteCertificate_7055⟩,
   ⟨7063,pellFiniteCertificate_7063⟩,
   ⟨7071,pellFiniteCertificate_7071⟩,
   ⟨7079,pellFiniteCertificate_7079⟩,
   ⟨7087,pellFiniteCertificate_7087⟩,
   ⟨7095,pellFiniteCertificate_7095⟩,
   ⟨7103,pellFiniteCertificate_7103⟩,
   ⟨7111,pellFiniteCertificate_7111⟩,
   ⟨7127,pellFiniteCertificate_7127⟩,
   ⟨7135,pellFiniteCertificate_7135⟩,
   ⟨7143,pellFiniteCertificate_7143⟩,
   ⟨7151,pellFiniteCertificate_7151⟩,
   ⟨7159,pellFiniteCertificate_7159⟩,
   ⟨7167,pellFiniteCertificate_7167⟩,
   ⟨7183,pellFiniteCertificate_7183⟩,
   ⟨7199,pellFiniteCertificate_7199⟩,
   ⟨7207,pellFiniteCertificate_7207⟩,
   ⟨7215,pellFiniteCertificate_7215⟩,
   ⟨7223,pellFiniteCertificate_7223⟩,
   ⟨7231,pellFiniteCertificate_7231⟩,
   ⟨7239,pellFiniteCertificate_7239⟩,
   ⟨7247,pellFiniteCertificate_7247⟩,
   ⟨7255,pellFiniteCertificate_7255⟩,
   ⟨7271,pellFiniteCertificate_7271⟩,
   ⟨7279,pellFiniteCertificate_7279⟩,
   ⟨7287,pellFiniteCertificate_7287⟩,
   ⟨7295,pellFiniteCertificate_7295⟩,
   ⟨7303,pellFiniteCertificate_7303⟩,
   ⟨7311,pellFiniteCertificate_7311⟩,
   ⟨7319,pellFiniteCertificate_7319⟩,
   ⟨7327,pellFiniteCertificate_7327⟩,
   ⟨7343,pellFiniteCertificate_7343⟩,
   ⟨7351,pellFiniteCertificate_7351⟩,
   ⟨7359,pellFiniteCertificate_7359⟩,
   ⟨7367,pellFiniteCertificate_7367⟩,
   ⟨7383,pellFiniteCertificate_7383⟩,
   ⟨7391,pellFiniteCertificate_7391⟩,
   ⟨7415,pellFiniteCertificate_7415⟩,
   ⟨7423,pellFiniteCertificate_7423⟩,
   ⟨7431,pellFiniteCertificate_7431⟩,
   ⟨7439,pellFiniteCertificate_7439⟩,
   ⟨7447,pellFiniteCertificate_7447⟩,
   ⟨7455,pellFiniteCertificate_7455⟩,
   ⟨7463,pellFiniteCertificate_7463⟩,
   ⟨7471,pellFiniteCertificate_7471⟩,
   ⟨7487,pellFiniteCertificate_7487⟩,
   ⟨7495,pellFiniteCertificate_7495⟩,
   ⟨7503,pellFiniteCertificate_7503⟩,
   ⟨7511,pellFiniteCertificate_7511⟩,
   ⟨7519,pellFiniteCertificate_7519⟩,
   ⟨7527,pellFiniteCertificate_7527⟩,
   ⟨7535,pellFiniteCertificate_7535⟩]

end D1Bound5


