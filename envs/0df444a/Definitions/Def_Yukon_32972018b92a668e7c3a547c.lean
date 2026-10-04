-- Prove2me | Definitions.Def_Yukon_32972018b92a668e7c3a547c
-- name    : Yukon_32972018b92a668e7c3a547c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T02:42:32.736913+00:00
-- url     : https://prove2.me/theorems/dbe1fbc0-788a-414c-b9f3-927563e55468
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceGeometricBudget6814.lean
--
--   yukon-proof-operation:certificate-b56-ae65a1f21e6067fe0767c28cc52a4264e6b7e27a804f614cd0d6e1a52263302b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTkyMjdhY2QwZTdjMjIxOTA5YWQ5NDBiZGY4ZmJjNGUxMTQ4OGY5ZTMxZmFhNmM4MzY1NDUzMGViODc1NDJmNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni1hZTY1YTFmMjFlNjA2N2ZlMDc2N2MyOGNjNTJhNDI2NGU2YjdlMjdhODA0ZjYxNGNkMGQ2ZTFhNTIyNjMzMDJiIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMzI5NzIwMThiOTJhNjY4ZTdjM2E1NDdjIiwidiI6Mn0]

import Definitions.Def_Yukon_b65780c687b1145241867ef4

import Definitions.Def_Yukon_6031b066ec5b1f25736844be













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! From the actual source pair and its carrier identities to a shared
pole/zero budget on the regular moving curves. Membership of the new cuts
is proved from the helper identities and the moving equation. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open RCN002 RCN095 RCN135 RCN136 RCN207 RCN237 RCN264 RCN313 RCN341
open SecondJetCoefficients SecondJetClearedHelper
open MovingSourceGenericCuts6814 MovingSourceCarrierZeros6814 MovingSourcePoleBudget6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))

def regularEquation (F : MvPolynomial (Fin 4) K)
    (quadratic A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F))
    (lift quadratic) (lift A) (initialCoordinate Omega)

def regularDenominator (F : MvPolynomial (Fin 4) K)
    (A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  surfaceMap phi (2*polyH K F) * lift (2*A)

abbrev MovingFamily (F : MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 3) OmegaT) (quadratic A : MvPolynomial (Fin 3) Omega) :=
  RegularComponent OmegaT G (regularEquation F quadratic A) (regularDenominator F A)






end
end ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814


