-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice14_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice14_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:56.342649+00:00
-- url     : https://prove2.me/theorems/55fddca8-f22f-41ea-8038-a27d02a6b843
-- title:
--   Exact Pell certificate records 897–960
-- statement:
--   The exact consecutive certificate records 897 through 960 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_015

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice14_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨8807,pellFiniteCertificate_8807⟩,
   ⟨8815,pellFiniteCertificate_8815⟩,
   ⟨8823,pellFiniteCertificate_8823⟩,
   ⟨8831,pellFiniteCertificate_8831⟩,
   ⟨8839,pellFiniteCertificate_8839⟩,
   ⟨8855,pellFiniteCertificate_8855⟩,
   ⟨8863,pellFiniteCertificate_8863⟩,
   ⟨8871,pellFiniteCertificate_8871⟩,
   ⟨8879,pellFiniteCertificate_8879⟩,
   ⟨8887,pellFiniteCertificate_8887⟩,
   ⟨8895,pellFiniteCertificate_8895⟩,
   ⟨8903,pellFiniteCertificate_8903⟩,
   ⟨8911,pellFiniteCertificate_8911⟩,
   ⟨8927,pellFiniteCertificate_8927⟩,
   ⟨8935,pellFiniteCertificate_8935⟩,
   ⟨8943,pellFiniteCertificate_8943⟩,
   ⟨8951,pellFiniteCertificate_8951⟩,
   ⟨8983,pellFiniteCertificate_8983⟩,
   ⟨8999,pellFiniteCertificate_8999⟩,
   ⟨9007,pellFiniteCertificate_9007⟩,
   ⟨9015,pellFiniteCertificate_9015⟩,
   ⟨9023,pellFiniteCertificate_9023⟩,
   ⟨9031,pellFiniteCertificate_9031⟩,
   ⟨9039,pellFiniteCertificate_9039⟩,
   ⟨9047,pellFiniteCertificate_9047⟩,
   ⟨9055,pellFiniteCertificate_9055⟩,
   ⟨9071,pellFiniteCertificate_9071⟩,
   ⟨9079,pellFiniteCertificate_9079⟩,
   ⟨9087,pellFiniteCertificate_9087⟩,
   ⟨9095,pellFiniteCertificate_9095⟩,
   ⟨9103,pellFiniteCertificate_9103⟩,
   ⟨9111,pellFiniteCertificate_9111⟩,
   ⟨9119,pellFiniteCertificate_9119⟩,
   ⟨9127,pellFiniteCertificate_9127⟩,
   ⟨9143,pellFiniteCertificate_9143⟩,
   ⟨9151,pellFiniteCertificate_9151⟩,
   ⟨9159,pellFiniteCertificate_9159⟩,
   ⟨9167,pellFiniteCertificate_9167⟩,
   ⟨9183,pellFiniteCertificate_9183⟩,
   ⟨9191,pellFiniteCertificate_9191⟩,
   ⟨9199,pellFiniteCertificate_9199⟩,
   ⟨9215,pellFiniteCertificate_9215⟩,
   ⟨9223,pellFiniteCertificate_9223⟩,
   ⟨9231,pellFiniteCertificate_9231⟩,
   ⟨9239,pellFiniteCertificate_9239⟩,
   ⟨9247,pellFiniteCertificate_9247⟩,
   ⟨9255,pellFiniteCertificate_9255⟩,
   ⟨9263,pellFiniteCertificate_9263⟩,
   ⟨9271,pellFiniteCertificate_9271⟩,
   ⟨9287,pellFiniteCertificate_9287⟩,
   ⟨9303,pellFiniteCertificate_9303⟩,
   ⟨9311,pellFiniteCertificate_9311⟩,
   ⟨9319,pellFiniteCertificate_9319⟩,
   ⟨9327,pellFiniteCertificate_9327⟩,
   ⟨9335,pellFiniteCertificate_9335⟩,
   ⟨9343,pellFiniteCertificate_9343⟩,
   ⟨9367,pellFiniteCertificate_9367⟩,
   ⟨9383,pellFiniteCertificate_9383⟩,
   ⟨9391,pellFiniteCertificate_9391⟩,
   ⟨9399,pellFiniteCertificate_9399⟩,
   ⟨9407,pellFiniteCertificate_9407⟩,
   ⟨9415,pellFiniteCertificate_9415⟩,
   ⟨9431,pellFiniteCertificate_9431⟩,
   ⟨9439,pellFiniteCertificate_9439⟩]

end D1Bound5


