-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice00_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice00_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:49.408646+00:00
-- url     : https://prove2.me/theorems/c2dc017b-7469-46e1-bfdb-5c14fe299381
-- title:
--   Exact Pell certificate records 1–64
-- statement:
--   The exact consecutive certificate records 1 through 64 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_001
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_002

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice00_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨7,pellFiniteCertificate_7⟩,
   ⟨15,pellFiniteCertificate_15⟩,
   ⟨23,pellFiniteCertificate_23⟩,
   ⟨31,pellFiniteCertificate_31⟩,
   ⟨39,pellFiniteCertificate_39⟩,
   ⟨47,pellFiniteCertificate_47⟩,
   ⟨55,pellFiniteCertificate_55⟩,
   ⟨71,pellFiniteCertificate_71⟩,
   ⟨79,pellFiniteCertificate_79⟩,
   ⟨87,pellFiniteCertificate_87⟩,
   ⟨95,pellFiniteCertificate_95⟩,
   ⟨103,pellFiniteCertificate_103⟩,
   ⟨111,pellFiniteCertificate_111⟩,
   ⟨119,pellFiniteCertificate_119⟩,
   ⟨127,pellFiniteCertificate_127⟩,
   ⟨143,pellFiniteCertificate_143⟩,
   ⟨151,pellFiniteCertificate_151⟩,
   ⟨159,pellFiniteCertificate_159⟩,
   ⟨167,pellFiniteCertificate_167⟩,
   ⟨183,pellFiniteCertificate_183⟩,
   ⟨191,pellFiniteCertificate_191⟩,
   ⟨199,pellFiniteCertificate_199⟩,
   ⟨215,pellFiniteCertificate_215⟩,
   ⟨223,pellFiniteCertificate_223⟩,
   ⟨231,pellFiniteCertificate_231⟩,
   ⟨239,pellFiniteCertificate_239⟩,
   ⟨247,pellFiniteCertificate_247⟩,
   ⟨255,pellFiniteCertificate_255⟩,
   ⟨263,pellFiniteCertificate_263⟩,
   ⟨271,pellFiniteCertificate_271⟩,
   ⟨287,pellFiniteCertificate_287⟩,
   ⟨295,pellFiniteCertificate_295⟩,
   ⟨303,pellFiniteCertificate_303⟩,
   ⟨311,pellFiniteCertificate_311⟩,
   ⟨319,pellFiniteCertificate_319⟩,
   ⟨327,pellFiniteCertificate_327⟩,
   ⟨335,pellFiniteCertificate_335⟩,
   ⟨359,pellFiniteCertificate_359⟩,
   ⟨367,pellFiniteCertificate_367⟩,
   ⟨383,pellFiniteCertificate_383⟩,
   ⟨391,pellFiniteCertificate_391⟩,
   ⟨399,pellFiniteCertificate_399⟩,
   ⟨407,pellFiniteCertificate_407⟩,
   ⟨415,pellFiniteCertificate_415⟩,
   ⟨431,pellFiniteCertificate_431⟩,
   ⟨439,pellFiniteCertificate_439⟩,
   ⟨447,pellFiniteCertificate_447⟩,
   ⟨455,pellFiniteCertificate_455⟩,
   ⟨463,pellFiniteCertificate_463⟩,
   ⟨471,pellFiniteCertificate_471⟩,
   ⟨479,pellFiniteCertificate_479⟩,
   ⟨487,pellFiniteCertificate_487⟩,
   ⟨503,pellFiniteCertificate_503⟩,
   ⟨511,pellFiniteCertificate_511⟩,
   ⟨519,pellFiniteCertificate_519⟩,
   ⟨527,pellFiniteCertificate_527⟩,
   ⟨535,pellFiniteCertificate_535⟩,
   ⟨543,pellFiniteCertificate_543⟩,
   ⟨551,pellFiniteCertificate_551⟩,
   ⟨559,pellFiniteCertificate_559⟩,
   ⟨583,pellFiniteCertificate_583⟩,
   ⟨591,pellFiniteCertificate_591⟩,
   ⟨599,pellFiniteCertificate_599⟩,
   ⟨607,pellFiniteCertificate_607⟩]

end D1Bound5


