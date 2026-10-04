-- Prove2me | Definitions.Def_Yukon_b9f61aed25b10510aa4d5321
-- name    : Yukon_b9f61aed25b10510aa4d5321
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T21:25:26.006986+00:00
-- url     : https://prove2.me/theorems/3cc303d9-92bf-4399-b028-48b1bc032122
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceReducedPrimary6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-897178536731d11ce48ef5219ab1524c286446f1748967ea4e02fef52c931180
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTRhMjIyYWNlZTA4YjNmZWNjZDRhYTE0NTQwYzIwYzFjNDRmZDYzNDAxYjUwYmQ5ZjkxNTVkMWQ5NzdiZjY0NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtODk3MTc4NTM2NzMxZDExY2U0OGVmNTIxOWFiMTUyNGMyODY0NDZmMTc0ODk2N2VhNGUwMmZlZjUyYzkzMTE4MCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2I5ZjYxYWVkMjViMTA1MTBhYTRkNTMyMSIsInYiOjJ9]

import Definitions.Def_Yukon_b9264d25766439028c5b06aa















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The smaller tail inherits the OLD intersection multiplicities on the
same primes. Only the OLD denominator must be regular for this one-way
inequality. No hypothesis about the new denominator, no equality of curve
families, and no assumed weighted count is used. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN248
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN120 RCN313
open MovingSourceFlowNumerator6814

/-- Cancellation in a primary thickening, not merely on its reduced
support. This is what retains the multiplicity in the resultant. -/
theorem primary_cross_transfer
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface oldTail newTail a b : R) (n : ℕ) (hn : 1≤n)
    (hsurface : surface∈J) (hb : b∉J)
    (hold : oldTail∈Ideal.span {surface} ⊔ J^n)
    (hcross : a*oldTail-b*newTail∈Ideal.span {surface}) :
    newTail∈Ideal.span {surface} ⊔ J^n := by
  let Q := Ideal.span {surface} ⊔ J^n
  have hprod : b*newTail∈Q := by
    have hc : a*oldTail-b*newTail∈Q :=
      (show Ideal.span {surface}≤Q from le_sup_left) hcross
    simpa only [sub_sub_cancel] using Q.sub_mem (Q.mul_mem_left a hold) hc
  exact RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
    surface newTail b J hsurface n hn hb hprod

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

/-- An actual stage supplies the old multiplicity; the proved denominator
cross-identity transfers it to the new numerator in every projected
primary piece. In particular the new denominator is NOT assumed a unit. -/
theorem reduced_tail_mem_projected_primary
    {B : Type*} [CommRing B]
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (C : FirstTailComponent S)
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (f : MvPolynomial (Fin 4) K →+* B)
    (surface : B) (J : Ideal B) [J.IsMaximal]
    (hfactor : f (originalData S C).factor∈Ideal.span {surface})
    (hsurface : surface∈J)
    (hcontract : Ideal.comap f J=componentPrime S C) :
    f (numerators H G (RCN326.w+1))∈Ideal.span {surface} ⊔
      J^localMultiplicity S (canonicalLocalDVRFamily S hfirst) C := by
  have hold := proper_global_tail_mem_projected_primary S hfirst C f surface
    (f (numerator K S.F (RCN326.w+1))) 1 J hfactor hsurface hcontract (mul_one _).symm
  have hF : f S.F∈Ideal.span {surface} := by
    rw [(originalData S C).product,map_mul]
    exact (Ideal.span {surface}).mul_mem_right _ hfactor
  have hdiff := (Ideal.span {surface}).mem_of_dvd (map_dvd f hcross) hF
  simp only [map_sub,map_mul,map_pow] at hdiff
  have hH : f (polyH K S.F)∉J := by
    intro hh
    have hp : polyH K S.F∈componentPrime S C := by
      rw [←hcontract]
      exact hh
    exact RCN312.firstTailComponent_regularity_not_mem S C hp
  have hpow : (f (polyH K S.F))^(2*(RCN326.w+1))∉J := by
    intro hh
    exact hH ((inferInstance : J.IsPrime).mem_of_pow_mem _ hh)
  exact primary_cross_transfer J surface _ _ _ _ _
    (one_le_localMultiplicity S hfirst C) hsurface hpow hold hdiff

/-- The indexed primary pieces are exactly the existing resultant
machinery's input, with the original component and multiplicity. -/
theorem indexed_reduced_tail_mem_primary
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    {A : Type} [Fintype A] (component : A → StageComponent S)
    (lam mu nu : GenericField K) (order : Fin 3 ≃ Fin 3)
    (ht : ∀ a, Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0))))
    (hfinite : ∀ a,
      letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1))
    (hgen : ∀ a,
      letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      IntermediateField.adjoin (RatFunc (GenericField K))
        ({flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 2)),
          flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 1))} :
          Set (CoordinateField (GenericField K) (component a).1))=⊤)
    (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) :
    indexedFiberTail q hq
        (RCN113.flagPlaneMap (GenericField K) lam mu nu order
          (surfaceMap (polynomialEmbedding K) (numerators H G (RCN326.w+1))))∈
      Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^
          localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a.1) := by
  let D := indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
  letI : (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal := D.relationMax
  exact reduced_tail_mem_projected_primary S hfirst (component a.1) H G hcross
    (stageFiberTargetMap S lam mu nu order q hq)
    (indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)) _
    D.factor_mem D.surface_mem D.contract







end
end ProximityPrize.SubmissionLower.MovingSourceReducedPrimary6814


