-- Prove2me | Definitions.Def_Yukon_6db579f0800634a21a2958ad
-- name    : Yukon_6db579f0800634a21a2958ad
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T00:41:22.605493+00:00
-- url     : https://prove2.me/theorems/e253db57-7350-4da6-bd1f-e2ece294ffdc
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceCoprimeCuts6814.lean
--
--   yukon-proof-operation:certificate-tail-1be3e93e362f2fa4410dbbac733b6b7114c3e0274c5b93e245fc23307bddaf96
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzllYmIyYzNjMDQxMGVlYTY0ODNhZjdjY2EwN2EyYjUxODFkNGQ5NWNkMjgzMTU0YmNhMmMyYWNlOGNmODZiMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtMWJlM2U5M2UzNjJmMmZhNDQxMGRiYmFjNzMzYjZiNzExNGMzZTAyNzRjNWI5M2UyNDVmYzIzMzA3YmRkYWY5NiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzZkYjU3OWYwODAwNjM0YTIxYTI5NThhZCIsInYiOjJ9]

import Definitions.Def_Yukon_10805ee98000946934f31f50

import Definitions.Def_Yukon_6d3add3a3f6938cc0bdd10e2

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Compose the algebraic clearing step for the actual source pair.
The moving target remains indeterminate; specialization is expressed by
an arbitrary coefficient evaluation and target value. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN135 RCN136 SecondJetCoefficients SecondJetClearedHelper
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceSaturation6814

variable (K : Type*) [Field K]
local notation "Omega" => GenericField K
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local instance  _root_.ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.instStrongNormalizationMonoidPolynomialMvPolynomialFinOfNatNatGenericField : StrongNormalizationMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance  _root_.ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.instNormalizedGCDMonoidPolynomialMvPolynomialFinOfNatNatGenericField : NormalizedGCDMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

def collectTarget (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) ≃ₐ[E] MvPolynomial (Fin 3) (Polynomial E) :=
  (MvPolynomial.finSuccEquiv E 3).symm.trans (RCN136.collectX E)

def genericTargetMap (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) →+* MvPolynomial (Fin 3) (GenericField E) :=
  (RCN136.surfaceMap (polynomialEmbedding E)).comp (MvPolynomial.finSuccEquiv E 3).symm.toRingHom

theorem genericTargetMap_injective (E : Type*) [Field E] :
    Function.Injective (genericTargetMap E) :=
  (RCN136.surfaceMap_injective (polynomialEmbedding E) (polynomialEmbedding_injective E)).comp
    (MvPolynomial.finSuccEquiv E 3).symm.injective

theorem genericTargetMap_relPrime (E : Type*) [Field E]
    (U V : Polynomial (MvPolynomial (Fin 3) E)) (hU : U≠0) (hrel : IsRelPrime U V) :
    IsRelPrime (genericTargetMap E U) (genericTargetMap E V) := by
  have hU' : collectTarget E U≠0 := by
    intro hz
    exact hU ((collectTarget E).injective (by simpa only [map_zero] using hz))
  exact generic_coefficient_map_relPrime E _ _ hU'
    (MovingSourceFlatBaseChange6814.isRelPrime_equiv (collectTarget E).toRingEquiv U V hrel)

theorem generic_coefficients_ne_zero (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) :
    coefficients (polynomialEmbedding K) P≠0 := by
  intro hz
  apply hP
  apply (asS (K := K)).injective
  apply Polynomial.map_injective (surfaceMap (polynomialEmbedding K))
    (surfaceMap_injective (polynomialEmbedding K) (polynomialEmbedding_injective K))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz

theorem generic_coefficients_degree (P : WholeSpaceCube6814.Poly (K := K)) (s : ℕ)
    (hS : P.degreeOf 1 ≤ s) : (coefficients (polynomialEmbedding K) P).natDegree ≤ s := by
  apply Polynomial.natDegree_map_le.trans
  simpa using SecondJetHelperWeights.asS_derivative_degree P s 0
    (MvPolynomial.degreeOf_le_iff.mp hS)










end
end ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814


