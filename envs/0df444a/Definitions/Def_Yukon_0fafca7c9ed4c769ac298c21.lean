-- Prove2me | Definitions.Def_Yukon_0fafca7c9ed4c769ac298c21
-- name    : Yukon_0fafca7c9ed4c769ac298c21
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T00:27:32.928499+00:00
-- url     : https://prove2.me/theorems/60ff10b2-bf99-46d8-b804-0adef67763c6
-- title:
--   LowerFoundation source section 3/9
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-parser-sections-Yukon_0fafca7c9ed4c769ac298c21
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTc2YzM3ZDg5MTk1OTJlM2Y5OWFmYjkyZWIzZTRkZWEzOWJkYTlkYTE1ODM5M2U3MDQ5YmQwNTcxMDBjMzY5MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tcGFyc2VyLXNlY3Rpb25zLVl1a29uXzBmYWZjYTdjOWVkNGM3NjlhYzI5OGMyMSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzBmYWZjYTdjOWVkNGM3NjlhYzI5OGMyMSIsInYiOjJ9]

import Definitions.Def_Yukon_9a4cb32b486d106f425c159a
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.C9. -/
section PackedLegacy_C9
namespace ProximityPrize.SubmissionLower.RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
@[reducible] def relationResidueAlgebra
   (J:Ideal (Polynomial R))
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R):
   Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
 (Ideal.quotientMap J (Polynomial.C:R →+*Polynomial R) (by
   rw [hcontract])).toAlgebra' (fun _ _ => mul_comm _ _)
theorem exists_monic_mem_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J)):
   ∃ H:Polynomial R,H.Monic∧H∈J:=by
 let k:=IsLocalRing.ResidueField R
 let E:=Polynomial R ⧸ J
 let qR:R →+*k:=Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
 let qB:Polynomial R →+*E:=Ideal.Quotient.mk J
 let aResidue:=relationResidueAlgebra J hcontract
 letI:Algebra k E:=aResidue
 let phi:k →+*E:=algebraMap k E
 letI:FiniteDimensional k E:=hfinite
 let y:E:=qB Polynomial.X
 let hbar:Polynomial k:=minpoly k y
 have hbarMonic:hbar.Monic:=
   minpoly.monic (IsIntegral.of_finite k y)
 have hbarLift:hbar∈Polynomial.lifts qR:=
   Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective hbar
 obtain ⟨H,hmap,hdegree,hHMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hbarLift hbarMonic
 have hcomp:(Polynomial.eval₂RingHom phi y).comp
     (Polynomial.mapRingHom qR)=qB:=by
   apply Polynomial.ringHom_ext
   · intro r
     simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_C,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
     change Ideal.Quotient.mk J (Polynomial.C r)=qB (Polynomial.C r)
     rfl
   · simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
     rfl
 have hHmem:H∈J:=by
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change qB H=0
   rw [←hcomp]
   change Polynomial.eval₂ phi y (H.map qR)=0
   rw [hmap]
   change Polynomial.aeval y hbar=0
   exact minpoly.aeval k y
 exact ⟨H,hHMonic,hHmem⟩
end
end ProximityPrize.SubmissionLower.RCN197
end PackedLegacy_C9

/-! Packed from ProximityPrize.SubmissionLower.L9. -/
section PackedLegacy_L9
namespace ProximityPrize.SubmissionLower.RCN192
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193 RCN120 RCN014 RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_comap_C_eq_maximalIdeal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap Polynomial.C=
     IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite):=by
 apply le_antisymm
 · apply IsLocalRing.le_maximalIdeal
   apply Ideal.comap_ne_top
   intro htop
   have hunder:=localizedRelation_under K L order e ht hfinite
   have hJne:relationKernel K L order e ht≠⊤:=RingHom.ker_ne_top _
   apply hJne
   rw [←hunder,htop,Ideal.comap_top]
 · exact maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite
theorem localizedRelationResidue_finite
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=
     targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   FiniteDimensional (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=by
 let F:=RatFunc K
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:Algebra F L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional F L:=hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let quotientSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=quotientSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 let phi:PlaneRing K →ₐ[F] L:={
   toRingHom:=planeEvaluation K L order e ht
   commutes':=fun a => by
     change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C a))=algebraMap F L a
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
 let eqv0:(PlaneRing K ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing K ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 letI:Module.Finite F (PlaneRing K ⧸ J):=
   Module.Finite.equiv eqv0.toLinearEquiv.symm
 letI:IsScalarTower F (AdjoinRoot q) (PlaneRing K ⧸ J):=
   IsScalarTower.of_algebraMap_eq fun c => by
     change Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))=
       Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))
     rfl
 letI:Module.Finite (AdjoinRoot q) (PlaneRing K ⧸ J):=
   Module.Finite.of_restrictScalars_finite F _ _
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 refine Module.Finite.of_equiv_equiv
   (A₁:=AdjoinRoot q) (B₁:=PlaneRing K ⧸ J)
   (A₂:=IsLocalRing.ResidueField Rp)
   (B₂:=LocalizedPlane K L order e ht hfinite ⧸ JP) e1 e2 ?_
 apply RingHom.ext
 intro x
 obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
 change Ideal.Quotient.mk JP
     (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
   Ideal.Quotient.mk JP
     (localizePlane K L order e ht hfinite (Polynomial.C x))
 apply congrArg (Ideal.Quotient.mk JP)
 change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
   Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
 rw [Polynomial.map_C]
theorem localizedRelationResidue_finrank_eq_unlocalized
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let q:=projectedFactor K L order e ht
   let J:=relationKernel K L order e ht
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
   let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a1:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   Module.finrank (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP)=
     Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J):=by
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 have hcompat:(algebraMap (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP)).comp e1.toRingHom=
     e2.toRingHom.comp (algebraMap (AdjoinRoot q) (PlaneRing K ⧸ J)):=by
   apply RingHom.ext
   intro x
   obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
   change Ideal.Quotient.mk JP
       (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
     Ideal.Quotient.mk JP
       (localizePlane K L order e ht hfinite (Polynomial.C x))
   apply congrArg (Ideal.Quotient.mk JP)
   change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
     Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
   rw [Polynomial.map_C]
 exact (Algebra.finrank_eq_of_equiv_equiv e1 e2 hcompat).symm
end
end ProximityPrize.SubmissionLower.RCN192
end PackedLegacy_L9

/-! Packed from ProximityPrize.SubmissionLower.FP. -/
section PackedLegacy_FP
namespace ProximityPrize.SubmissionLower.RCN236
open RCN014 RCN225 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 {J:Type*} [Fintype J]
noncomputable def primaryPiecesCertificateOfMembershipWeighted
   [IsLocalRing R]
   (surface tail:Polynomial R)
   [hSurfacePrime:(Ideal.span {surface}).IsPrime]
   (relation:J → Ideal (Polynomial R))
   (relationBar:J → Ideal (SurfaceQuotient surface))
   [∀ j,(relationBar j).IsMaximal]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBar:∀ j,relationBar j=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) (relation j))
   (hrelationBarNe:∀ j,relationBar j≠⊥)
   [∀ j,IsLocalHom
     (algebraMap R (Localization.AtPrime (relationBar j)))]
   [∀ j,FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))]
   (mu:J → ℕ)
   (htail:∀ j,tail∈Ideal.span {surface} ⊔ relation j^mu j)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j)):
   PrimaryPiecesCertificate surface tail (fun j↦
     mu j*Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))) where
 pieces j:=mappedPrimaryPiece (RingHom.id (Polynomial R)) relation
   surface mu j
 coprime:=mappedPrimaryPiece_pairwise_coprime
   (RingHom.id (Polynomial R)) relation hcoprime surface mu
 contains j:=by
   apply span_pair_le_mappedPrimaryPiece
     (RingHom.id (Polynomial R)) relation surface tail mu j
   simpa only [mappedPrimaryPiece,Ideal.map_id] using htail j
 length_le j:=by
   have hmap:Ideal.map (RingHom.id (Polynomial R)) (relation j)=relation j:=
     Ideal.map_id (relation j)
   have hbound:=
     exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
       (R:=R) surface (relation j) (relationBar j)
         (hrelationBar j) (hrelationBarNe j) (mu j)
   change ((mu j*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j))):ℕ):ℕ∞) ≤
       Module.length R (Polynomial R ⧸ (Ideal.span {surface} ⊔
         Ideal.map (RingHom.id (Polynomial R)) (relation j)^mu j))
   rw [hmap]
   exact hbound
end
end ProximityPrize.SubmissionLower.RCN236
end PackedLegacy_FP
end Compact_PackedLegacy


