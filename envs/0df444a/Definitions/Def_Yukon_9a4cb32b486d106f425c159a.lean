-- Prove2me | Definitions.Def_Yukon_9a4cb32b486d106f425c159a
-- name    : Yukon_9a4cb32b486d106f425c159a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T00:23:27.358951+00:00
-- url     : https://prove2.me/theorems/ee946904-ea18-469e-a820-c581f023b86a
-- title:
--   LowerFoundation source section 2/9
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-parser-sections-Yukon_9a4cb32b486d106f425c159a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjdiMTdmNTk5ZjM2YmIwMTZlMDBlZTg3MmRjMWZmMGE2YmM3NGIyMGJlMzc1MGMwN2U4ZWExYzEwMDkyMWFiNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tcGFyc2VyLXNlY3Rpb25zLVl1a29uXzlhNGNiMzJiNDg2ZDEwNmY0MjVjMTU5YSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzlhNGNiMzJiNDg2ZDEwNmY0MjVjMTU5YSIsInYiOjJ9]

import Definitions.Def_Yukon_78d3dab0dca745c88dfa0dfd
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.C8. -/
section PackedLegacy_C8
namespace ProximityPrize.SubmissionLower.RCN193
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_under
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap
     (localizePlane K L order e ht hfinite)=
     relationKernel K L order e ht:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=Polynomial.isLocalization p.primeCompl Rp
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K)) (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).comap
   (algebraMap (PlaneRing K) (Polynomial Rp))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial Rp) hJprime hdisjoint
noncomputable def planeResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (PlaneRing K ⧸ relationKernel K L order e ht) ≃+*
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*S:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hJPmax:JP.IsMaximal:=localizedRelation_isMaximal
   K L order e ht hfinite hgen
 letI:JP.IsPrime:=hJPmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra S Sp:=Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) Sp:=
   Polynomial.isLocalization p.primeCompl Rp
 have hunder:JP.comap f=J:=localizedRelation_under K L order e ht hfinite
 have hf:f=algebraMap S Sp:=rfl
 have hunderAlg:JP.under S=J:=by
   change JP.comap (algebraMap S Sp)=J
   rw [←hf]
   exact hunder
 let g:(S ⧸ J) →+*(Sp ⧸ JP):=
   Ideal.quotientMap JP (algebraMap S Sp) hunderAlg.ge
 refine RingEquiv.ofBijective g ⟨?_,?_⟩
 · exact Ideal.quotientMap_injective' hunderAlg.le
 · exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
     (p.primeCompl.map c.toMonoidHom) Sp (J:=J) (I:=JP)
       (H:=hunderAlg.ge) (hunderAlg ▸ hJmax)
@[simp] theorem planeResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (x:PlaneRing K):
   planeResidueEquiv K L order e ht hfinite hgen
       (Ideal.Quotient.mk (relationKernel K L order e ht) x)=
     Ideal.Quotient.mk (localizedRelation K L order e ht hfinite)
       (localizePlane K L order e ht hfinite x):=rfl
theorem maximalIdeal_le_localizedRelation_comap_C
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite) ≤
     (localizedRelation K L order e ht hfinite).comap Polynomial.C:=by
 let C:=Polynomial (RatFunc K)
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let a:C →+*Rp:=algebraMap C Rp
 let c:C →+*S:=Polynomial.C
 let cL:Rp →+*Sp:=Polynomial.C
 let f:S →+*Sp:=localizePlane K L order e ht hfinite
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra C Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 have hcontract:J.comap c=p:=by
   simpa only [J,c,p] using relationKernel_comap_C K L order e ht
 have hsquare:cL.comp a=f.comp c:=by
   apply DFunLike.ext _ _
   intro x
   change Polynomial.C (a x)=Polynomial.map a (Polynomial.C x)
   rw [Polynomial.map_C]
 rw [←IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
   ←Ideal.map_le_iff_le_comap]
 calc
   Ideal.map cL (Ideal.map a p)=Ideal.map (cL.comp a) p:=
     Ideal.map_map a cL
   _=Ideal.map (f.comp c) p:=by
     rw [hsquare]
   _=Ideal.map f (Ideal.map c p):=(Ideal.map_map c f).symm
   _ ≤ Ideal.map f J:=Ideal.map_mono
     (Ideal.map_le_iff_le_comap.mpr hcontract.ge)
   _=JP:=rfl
@[reducible] def localizedResidueAlgebra
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Algebra
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=
 Ideal.Quotient.algebraQuotientOfLEComap
   (maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite)
noncomputable def coefficientResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   AdjoinRoot (projectedFactor K L order e ht) ≃+*
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite)):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 letI:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 change (Polynomial (RatFunc K) ⧸ p) ≃+*
   (Rp ⧸ IsLocalRing.maximalIdeal Rp)
 exact IsLocalization.AtPrime.equivQuotMaximalIdeal p Rp
@[simp] theorem coefficientResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (x:Polynomial (RatFunc K)):
   coefficientResidueEquiv K L order e ht hfinite
       (AdjoinRoot.mk (projectedFactor K L order e ht) x)=
     Ideal.Quotient.mk
       (IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
       (algebraMap (Polynomial (RatFunc K))
         (LocalCoefficient K L order e ht hfinite) x):=rfl
end
end ProximityPrize.SubmissionLower.RCN193
end PackedLegacy_C8

/-! Packed from ProximityPrize.SubmissionLower.M0. -/

/- Library component D7 is loaded from Mathlib.RingTheory.OrderOfVanishing.Basic. -/

/-! Packed from ProximityPrize.SubmissionLower.M2. -/
section PackedLegacy_M2
namespace ProximityPrize.SubmissionLower.RCN196
open scoped Classical BigOperators
open Module
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R M ι:Type*}
 [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
public theorem ord_finset_prod
   (a:ι → R) (ha:∀ i,a i≠0):
   Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=by
 classical
 let s:Finset ι:=Finset.univ
 change Ring.ord R (∏ i∈s,a i)=∑ i∈s,Ring.ord R (a i)
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih =>
     rw [Finset.prod_insert hi,Finset.sum_insert hi,
       Ring.ord_mul' (R:=R)
         (mem_nonZeroDivisors_iff_ne_zero.mpr (ha i)),ih]
theorem associated_det_prod_smithRange
   (b:Basis ι R M) (f:M →ₗ[R] M) (hinj:Function.Injective f):
   Associated (LinearMap.det f)
     (∏ i,(LinearMap.range f).smithNormalFormCoeffs b
       (f.finrank_range_of_inj hinj) i):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let bM:Basis ι R M:=N.smithNormalFormTopBasis b hrank
 let bN:Basis ι R N:=N.smithNormalFormBotBasis b hrank
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 let eActual:M ≃ₗ[R] N:=LinearEquiv.ofInjective f hinj
 let eSmith:M ≃ₗ[R] N:=bM.equiv bN (Equiv.refl ι)
 let g:M →ₗ[R] M:=N.subtype.comp eSmith.toLinearMap
 have hmatrix:LinearMap.toMatrix bM bM g=Matrix.diagonal a:=by
   ext i j
   simp only [LinearMap.toMatrix_apply,g,LinearMap.comp_apply,
     LinearEquiv.coe_coe,eSmith,Basis.equiv_apply,Equiv.refl_apply]
   have hsnf:((bN j:N):M)=a j • bM j:=by
     exact N.smithNormalFormBotBasis_def b hrank j
   change bM.repr ((bN j:N):M) i=
     if i=j then a i else 0
   rw [hsnf,map_smul,Basis.repr_self,Finsupp.smul_single]
   by_cases hij:i=j
   · subst j
     simp
   · simp [Finsupp.single_apply,hij]
 have hdetg:LinearMap.det g=∏ i,a i:=by
   calc
     LinearMap.det g=(LinearMap.toMatrix bM bM g).det:=
       (LinearMap.det_toMatrix bM g).symm
     _=(Matrix.diagonal a).det:=by rw [hmatrix]
     _=∏ i,a i:=Matrix.det_diagonal
 have hassoc:Associated (LinearMap.det f) (LinearMap.det g):=by
   have h:=LinearMap.associated_det_comp_equiv N.subtype eActual eSmith
   have heActual:N.subtype.comp eActual.toLinearMap=f:=by
     ext z
     exact LinearEquiv.ofInjective_apply (h:=hinj) f z
   rw [heActual] at h
   exact h
 simpa only [N,hrank,a,hdetg] using hassoc
theorem length_coker_eq_ord_det
   (b:Basis ι R M) (f:M →ₗ[R] M)
   (hinj:Function.Injective f):
   Module.length R (M ⧸ LinearMap.range f)=Ring.ord R (LinearMap.det f):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 have ha:∀ i,a i≠0:=fun i => N.smithNormalFormCoeffs_ne_zero b hrank i
 have hdecomp:Module.length R (M ⧸ N)=
     ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=by
   rw [(N.quotientEquivPiSpan b hrank).length_eq,
     Module.length_pi_of_fintype R]
 have hprod:Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=
   ord_finset_prod a ha
 have hassoc:Associated (LinearMap.det f) (∏ i,a i):=by
   simpa only [N,hrank,a] using associated_det_prod_smithRange b f hinj
 change Module.length R (M ⧸ N)=_
 calc
   Module.length R (M ⧸ N)=
       ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=hdecomp
   _=∑ i,Ring.ord R (a i):=rfl
   _=Ring.ord R (∏ i,a i):=hprod.symm
   _=Ring.ord R (LinearMap.det f):=
     (Ring.ord_eq_of_associated hassoc).symm
section TwoModules
variable {N:Type*} [AddCommGroup N] [Module R N]
theorem length_coker_eq_ord_toMatrix_det
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f):
   Module.length R (N ⧸ LinearMap.range f)=
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 classical
 let e:N ≃ₗ[R] M:=bN.equiv bM (Equiv.refl ι)
 let g:N →ₗ[R] N:=f.comp e.toLinearMap
 have hginj:Function.Injective g:=hinj.comp e.injective
 have hrange:LinearMap.range g=LinearMap.range f:=by
   change LinearMap.range (f.comp e.toLinearMap)=LinearMap.range f
   rw [LinearMap.range_comp_of_range_eq_top f e.range]
 have hmatrix:LinearMap.toMatrix bN bN g=
     LinearMap.toMatrix bM bN f:=by
   change LinearMap.toMatrix bN bN (f.comp e.toLinearMap)=_
   rw [LinearMap.toMatrix_comp bN bM bN,
     LinearMap.toMatrix_basis_equiv,Matrix.mul_one]
 calc
   Module.length R (N ⧸ LinearMap.range f)=
       Module.length R (N ⧸ LinearMap.range g):=by rw [hrange]
   _=Ring.ord R (LinearMap.det g):=length_coker_eq_ord_det bN g hginj
   _=Ring.ord R (LinearMap.toMatrix bN bN g).det:=by
     rw [LinearMap.det_toMatrix]
   _=Ring.ord R (LinearMap.toMatrix bM bN f).det:=by rw [hmatrix]
theorem sum_multiplicities_le_ord_toMatrix_det_of_surjective
   {J:Type*} [Fintype J]
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f)
   (pieces:J → Type*)
   [∀ j,AddCommGroup (pieces j)] [∀ j,Module R (pieces j)]
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤ Module.length R (pieces j))
   (project:(N ⧸ LinearMap.range f) →ₗ[R] (∀ j,pieces j))
   (hsurj:Function.Surjective project):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 rw [←length_coker_eq_ord_toMatrix_det bM bN f hinj]
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞)=
       ∑ j,(multiplicity j:ℕ∞):=by simp
   _ ≤ ∑ j,Module.length R (pieces j):=
     Finset.sum_le_sum (fun j _ => hlength j)
   _=Module.length R (∀ j,pieces j):=
     (Module.length_pi_of_fintype R pieces).symm
   _ ≤ Module.length R (N ⧸ LinearMap.range f):=
     Module.length_le_of_surjective project hsurj
end TwoModules
end
end ProximityPrize.SubmissionLower.RCN196
end PackedLegacy_M2

/-! Packed from ProximityPrize.SubmissionLower.CE. -/
section PackedLegacy_CE
namespace ProximityPrize.SubmissionLower.RCN307
noncomputable section
set_option autoImplicit false
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
def intersectionIdeal (P Q:Polynomial R):Ideal (Polynomial R):=
 Ideal.span {P,Q}
structure PrimaryPiecesCertificate
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (multiplicity:J → ℕ) where
 pieces:J → Ideal (Polynomial R)
 coprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j)
 contains:∀ j,intersectionIdeal P Q ≤ pieces j
 length_le:∀ j,(multiplicity j:ℕ∞) ≤
   Module.length R (Polynomial R ⧸ pieces j)
end
end ProximityPrize.SubmissionLower.RCN307
end PackedLegacy_CE

/-! Packed from ProximityPrize.SubmissionLower.CF. -/
section PackedLegacy_CF
namespace ProximityPrize.SubmissionLower.RCN309
open scoped Classical BigOperators
open Module RCN196 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
theorem moduleFinite_quotient_of_monic_mem
   (I:Ideal (Polynomial R)) (M:Polynomial R)
   (hMMonic:M.Monic) (hMmem:M∈I):
   Module.Finite R (Polynomial R ⧸ I):=by
 let hle:Ideal.span {M} ≤ I:=Ideal.span_le.mpr (by simpa)
 let f:(Polynomial R ⧸ Ideal.span {M}) →ₐ[R]
     (Polynomial R ⧸ I):=Ideal.Quotient.factorₐ R hle
 letI:Module.Finite R (Polynomial R ⧸ Ideal.span {M}):=
   hMMonic.finite_quotient
 exact Module.Finite.of_surjective f.toLinearMap
   (Ideal.Quotient.factor_surjective hle)
def rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R)):
   Polynomial.degreeLT R (m+n) →ₗ[R]
     (∀ j,Polynomial R ⧸ pieces j):=
 LinearMap.pi fun j↦
   ((Submodule.mkQ (pieces j)).restrictScalars R).comp
     (Submodule.subtype (Polynomial.degreeLT R (m+n)))
theorem range_sylvesterMap_le_ker_rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap) ≤
     LinearMap.ker (rawPiecesMap P Q m n pieces):=by
 rintro y ⟨v,rfl⟩
 rw [LinearMap.mem_ker]
 funext j
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 apply hcontains j
 change P*(v.2:Polynomial R)+Q*(v.1:Polynomial R)∈
   intersectionIdeal P Q
 exact Ideal.add_mem _
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert P {Q})))
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert_of_mem P (Set.mem_singleton Q))))
def cokerToPieces
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   (Polynomial.degreeLT R (m+n) ⧸
     LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)) →ₗ[R]
       (∀ j,Polynomial R ⧸ pieces j):=
 (LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)).liftQ
   (rawPiecesMap P Q m n pieces)
   (range_sylvesterMap_le_ker_rawPiecesMap
     P Q m n hPcap hQcap pieces hcontains)
theorem cokerToPieces_surjective_of_modMax
   [IsLocalRing R]
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces))):
   Function.Surjective
     (cokerToPieces P Q m n hPcap hQcap pieces hcontains):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hraw:Function.Surjective (rawPiecesMap P Q m n pieces):=by
   apply LinearMap.surjective_of_surjective_comp_mkQ
     (rawPiecesMap P Q m n pieces) (IsLocalRing.maximalIdeal R)
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
   exact hmod
 intro y
 obtain ⟨v,hv⟩:=hraw y
 refine ⟨Submodule.Quotient.mk v,?_⟩
 change rawPiecesMap P Q m n pieces v=y
 exact hv
end
end ProximityPrize.SubmissionLower.RCN309
end PackedLegacy_CF
end Compact_PackedLegacy


