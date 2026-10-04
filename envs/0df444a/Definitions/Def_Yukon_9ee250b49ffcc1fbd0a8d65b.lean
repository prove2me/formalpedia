-- Prove2me | Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b
-- name    : Yukon_9ee250b49ffcc1fbd0a8d65b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:59:07.79465+00:00
-- url     : https://prove2.me/theorems/01cd3199-35f7-4f1c-9032-c123a5e99023
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceWholeCarrier6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-9be5443295caf92e6e31cc8b648909bc0f0c317fc45da95b9eeb13697fa76721
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODhiZDQwYWEwM2RjYTMyNjExMDU0OTY1NTVhMmZmZjliMmM1NTNhMjZlYmMzZGE5YWFhNGIzMjM5NTUxYmRiOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtOWJlNTQ0MzI5NWNhZjkyZTZlMzFjYzhiNjQ4OTA5YmMwZjBjMzE3ZmM0NWRhOTViOWVlYjEzNjk3ZmE3NjcyMSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzllZTI1MGI0OWZmY2MxZmJkMGE4ZDY1YiIsInYiOjJ9]

import Definitions.Def_Yukon_5bee0eb731f90d2a0bcf4c44













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Use the full specialized carrier, without selecting or separately
charging its geometric irreducible factors. One constructed source pair
contains every regular moving curve and supplies one shared budget. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN002 RCN046 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN264 RCN313 RCN341
open SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceGenericCuts6814 MovingSourceCarrierZeros6814 MovingSourceCarrierField6814
open MovingSourceGeometricBudget6814 MovingSourceAutomaticProjection6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))

def wholeCarrier (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 3) OmegaT := surfaceMap phi F

abbrev WholeMovingFamily (F : MvPolynomial (Fin 4) K)
    (quadratic A : MvPolynomial (Fin 3) Omega) := MovingFamily F (wholeCarrier F) quadratic A

theorem wholeCarrier_injective : Function.Injective (wholeCarrier (K:=K)) :=
  surfaceMap_injective phi ((coefficientEmbedding Omega).injective.comp (polynomialEmbedding_injective K))

theorem wholeCarrier_derivative_nonzero [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    MvPolynomial.pderiv (1 : Fin 3) (wholeCarrier F)≠0 := by
  rw [wholeCarrier,RCN267.surfaceMap_pderiv_R]
  intro hz
  apply RCN267.R_derivative_nonzero F 2130706433 hpos hsmall
  apply wholeCarrier_injective
  simpa only [wholeCarrier,map_zero] using hz











end
end ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814


