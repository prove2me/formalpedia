-- Prove2me | Definitions.Def_Yukon_7fa2e9b1f92d4b5807689791
-- name    : Yukon_7fa2e9b1f92d4b5807689791
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:08:14.936953+00:00
-- url     : https://prove2.me/theorems/171b2ed9-9a48-4f0c-bdc5-46126e8ea7ea
-- title:
--   LowerFoundation source part 4/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:foundation-direct-aa9d371514c8f4bd46ea8fb96ddae52f470ff6b9a25a346f4ee796aa30888c7c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTAwYTQ5MzExYTg5ZGNkZDc3ODMyN2Y5Y2E1NzI5ZmY1M2NiMDMxYzE2MGI5MDY0NTc3MjYyZjZmOTQyZmY1YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWFhOWQzNzE1MTRjOGY0YmQ0NmVhOGZiOTZkZGFlNTJmNDcwZmY2YjlhMjVhMzQ2ZjRlZTc5NmFhMzA4ODhjN2MiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83ZmEyZTliMWY5MmQ0YjU4MDc2ODk3OTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_031fc7732b9b4aeb0f27d711






















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.GK. -/
section PackedLegacy_GK
namespace ProximityPrize.SubmissionLower.RCN308
open scoped Classical
open RCN307 RCN309
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
def fullPiecesRingHom
   {J:Type*} [Fintype J]
   (pieces:J → Ideal (Polynomial R)):
   Polynomial R →+*(∀ j,Polynomial R ⧸ pieces j):=
 RingHom.pi fun j↦Ideal.Quotient.mk (pieces j)
def coefficientMaxIdeal:Ideal (Polynomial R):=
 Ideal.map (Polynomial.C:R →+*Polynomial R)
   (IsLocalRing.maximalIdeal R)
theorem rawPieces_modMax_surjective_of_monic_mod
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R))
   (hcoprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   (M:Polynomial R) (hMMonic:M.Monic)
   (hMmem:M∈intersectionIdeal P Q ⊔ coefficientMaxIdeal (R:=R))
   (hMdegree:M.natDegree ≤ m+n):
   Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let full:=fullPiecesRingHom pieces
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hfullC:full.comp (Polynomial.C:R →+*Polynomial R)=
     algebraMap R target:=by
   ext r j
   rfl
 have hcoeffMap:Ideal.map full (coefficientMaxIdeal (R:=R))=
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   rw [coefficientMaxIdeal,Ideal.map_map,hfullC]
 have hinterZero:∀ x∈intersectionIdeal P Q,full x=0:=by
   intro x hx
   funext j
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcontains j hx)
 have hMmax:full M∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp hMmem
   have hfa:full a=0:=hinterZero a ha
   have hfb:full b∈
       Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
     rw [←hcoeffMap]
     exact Ideal.mem_map_of_mem full hb
   rw [←hab,map_add,hfa,zero_add]
   exact hfb
 intro ybar
 obtain ⟨y,rfl⟩:=Submodule.mkQ_surjective maxTarget ybar
 obtain ⟨A,hA⟩:=Ideal.pi_mkQ_surjective hcoprime y
 let rem:Polynomial R:=A %ₘ M
 have hremDegree:rem.degree < (m+n:ℕ):=by
   have hlt:=Polynomial.degree_modByMonic_lt A hMMonic
   rw [Polynomial.degree_eq_natDegree hMMonic.ne_zero] at hlt
   exact hlt.trans_le (by exact_mod_cast hMdegree)
 let v:Polynomial.degreeLT R (m+n):=
   ⟨rem,Polynomial.mem_degreeLT.mpr hremDegree⟩
 refine ⟨v,?_⟩
 change maxTarget.mkQ (rawPiecesMap P Q m n pieces v)=maxTarget.mkQ y
 rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
 have hraw:rawPiecesMap P Q m n pieces v=full rem:=by
   rfl
 have hfullA:full A=y:=hA
 rw [hraw, ←hfullA, ←map_sub]
 have hdiff:rem-A= -(M*(A/ₘ M)):=by
   dsimp only [rem]
   rw [Polynomial.modByMonic_eq_sub_mul_div]
   ring
 rw [hdiff,map_neg,map_mul]
 have hmul:full M*full (A/ₘ M)∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=
   Ideal.mul_mem_right _ _ hMmax
 have hmul':full M*full (A/ₘ M)∈maxTarget:=by
   change full M*full (A/ₘ M)∈
     IsLocalRing.maximalIdeal R • (⊤:Submodule R target)
   rw [Ideal.smul_top_eq_map]
   exact hmul
 exact maxTarget.neg_mem hmul'
theorem sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)))
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤
     Module.length R (Polynomial R ⧸ pieces j)):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (Polynomial.resultant P Q m n):=by
 classical
 letI:DecidableEq (Fin (m+n)):=Classical.decEq _
 let f:=Polynomial.sylvesterMap P Q hPcap hQcap
 have hinj:Function.Injective f:=by
   intro x y hxy
   apply sub_eq_zero.mp
   let z:=x-y
   have hfz:f z=0:=by simp [z,f,hxy]
   have hcomp:=LinearMap.congr_fun
     (Polynomial.adjSylvester_comp_sylveserMap P Q hPcap hQcap) z
   have hscalar:Polynomial.resultant P Q m n • z=0:=by
     rw [LinearMap.comp_apply,hfz,map_zero] at hcomp
     simpa using hcomp.symm
   exact (smul_eq_zero.mp hscalar).resolve_left hresultant
 have hbound:=
   RCN196.sum_multiplicities_le_ord_toMatrix_det_of_surjective
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f hinj
     (fun j↦Polynomial R ⧸ pieces j) multiplicity hlength
     (RCN309.cokerToPieces
       P Q m n hPcap hQcap pieces hcontains)
     (cokerToPieces_surjective_of_modMax P Q m n hPcap hQcap
       pieces hcontains hmod)
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f=
       Polynomial.sylvester P Q m n:=by
   ext i j
   obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
   simpa [f,Polynomial.degreeLT.basisProd,LinearMap.toMatrix_apply] using
     congr($(Polynomial.toMatrix_sylvesterMap P Q hPcap hQcap) i j)
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
       Ring.ord R (LinearMap.toMatrix
         (Polynomial.degreeLT.basisProd R m n)
         (Polynomial.degreeLT.basis R (m+n)) f).det:=hbound
   _=Ring.ord R (Polynomial.resultant P Q m n):=by
     rw [hmatrix]
     congr 1
     unfold Polynomial.resultant
     convert! rfl
end
end ProximityPrize.SubmissionLower.RCN308
end PackedLegacy_GK

/-! Packed from ProximityPrize.SubmissionLower.GB. -/
section PackedLegacy_GB
namespace ProximityPrize.SubmissionLower.RCN297
open RCN307 RCN308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type*} [CommRing R] [IsLocalRing R]
theorem exists_specialized_monic_reducer
   (P:Polynomial R)
   (hPbar:P.map (IsLocalRing.residue R)≠0):
   ∃ M:Polynomial R,
     M.Monic∧
     M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)∧
     M.natDegree ≤ P.natDegree:=by
 let k:=IsLocalRing.ResidueField R
 let q:R →+*k:=IsLocalRing.residue R
 let Pbar:Polynomial k:=P.map q
 let Mbar:Polynomial k:=Pbar*Polynomial.C Pbar.leadingCoeff⁻¹
 have hMbarMonic:Mbar.Monic:=
   Polynomial.monic_mul_leadingCoeff_inv hPbar
 have hMbarLift:Mbar∈Polynomial.lifts q:=
   Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) Mbar
 obtain ⟨M,hMmap,hMdegree,hMMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hMbarLift hMbarMonic
 obtain ⟨c,hc⟩:=IsLocalRing.residue_surjective Pbar.leadingCoeff⁻¹
 change q c=Pbar.leadingCoeff⁻¹ at hc
 let D:Polynomial R:=M-Polynomial.C c*P
 have hDmap:D.map q=0:=by
   dsimp only [D]
   rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
     hMmap,hc]
   dsimp only [Mbar]
   ring
 have hDcoeff:D∈coefficientMaxIdeal (R:=R):=by
   have hker:D∈RingHom.ker (Polynomial.mapRingHom q):=hDmap
   rw [Polynomial.ker_mapRingHom,IsLocalRing.ker_residue] at hker
   exact hker
 have hMmem:M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=by
   have hfirst:Polynomial.C c*P∈Ideal.span {P}:=
     (Ideal.span {P}).mul_mem_left _
       (Ideal.subset_span (Set.mem_singleton P))
   have hfirst':Polynomial.C c*P∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show Ideal.span {P} ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_left) hfirst
   have hDcoeff':D∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show coefficientMaxIdeal (R:=R) ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_right) hDcoeff
   have hadd:=(Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)).add_mem
     hfirst' hDcoeff'
   convert hadd using 1 <;>
     simp only [D] <;> ring
 have hdegreeBar:Mbar.natDegree=Pbar.natDegree:=
   Polynomial.natDegree_mul_leadingCoeff_inv Pbar hPbar
 refine ⟨M,hMMonic,hMmem,?_⟩
 rw [hMdegree,hdegreeBar]
 exact Polynomial.natDegree_map_le
end
end ProximityPrize.SubmissionLower.RCN297
end PackedLegacy_GB

/-! Packed from ProximityPrize.SubmissionLower.EP. -/
section PackedLegacy_EP
namespace ProximityPrize.SubmissionLower.RCN143
open scoped Classical BigOperators
open RCN227 RCN307 RCN309 RCN308 RCN297
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Base:Type} [Field Base] [DecidableEq Base]
variable (primeIdeal:Ideal (Polynomial Base)) [primeIdeal.IsPrime]
 (factor:Polynomial Base)
abbrev LocalBase:=Localization.AtPrime primeIdeal
theorem grouped_resultant_power_dvd_of_primary_pieces_modMax
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal (LocalBase primeIdeal) •
         (⊤:Submodule (LocalBase primeIdeal)
           (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j))).mkQ).comp
       (rawPiecesMap P Q m n C.pieces))):
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 have hp0:primeIdeal≠⊥:=by
   rw [hprime,ne_eq,Ideal.span_singleton_eq_bot]
   exact hfactor.ne_zero
 letI:IsDiscreteValuationRing (LocalBase primeIdeal):=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial Base) hp0 _
 have hmappedResultant:Polynomial.resultant P Q m n=
     algebraMap (Polynomial Base) (LocalBase primeIdeal)
       (Polynomial.resultant P₀ Q₀ m n):=by
   rw [hPmap,hQmap,Polynomial.resultant_map_map]
 have hmappedNe:Polynomial.resultant P Q m n≠0:=by
   rw [hmappedResultant]
   simpa only [map_zero] using
     (FaithfulSMul.algebraMap_injective
       (Polynomial Base) (LocalBase primeIdeal)).ne hresultant
 have hlocal:=
   sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
     P Q m n hPcap hQcap hmappedNe C.pieces C.contains hmod
       multiplicity C.length_le
 have hlocal':
     (((∑ j,multiplicity j:ℕ):ℕ∞)) ≤
       Ring.ord (LocalBase primeIdeal)
         (algebraMap (Polynomial Base) (LocalBase primeIdeal)
           (Polynomial.resultant P₀ Q₀ m n)):=by
   rw [←hmappedResultant]
   exact hlocal
 exact pow_sum_dvd_of_sum_le_localized_ord primeIdeal factor
   (Polynomial.resultant P₀ Q₀ m n) hprime hfactor hfactorMonic
     hresultant multiplicity hlocal'
theorem grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (hPbar:P.map (IsLocalRing.residue (LocalBase primeIdeal))≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]:
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 obtain ⟨M,hMMonic,hMmem,hMdegreeP⟩:=
   exists_specialized_monic_reducer P hPbar
 have hspan:Ideal.span {P} ≤ intersectionIdeal P Q:=by
   rw [Ideal.span_le]
   intro x hx
   rw [Set.mem_singleton_iff] at hx
   subst x
   exact Ideal.subset_span (Set.mem_insert P {Q})
 have hMmem':M∈intersectionIdeal P Q ⊔
     coefficientMaxIdeal (R:=LocalBase primeIdeal):=
   (sup_le_sup hspan le_rfl) hMmem
 have hMdegree:M.natDegree ≤ m+n:=
   hMdegreeP.trans (hPcap.trans (Nat.le_add_right m n))
 have hmod:=rawPieces_modMax_surjective_of_monic_mod
   P Q m n C.pieces C.coprime C.contains M hMMonic hMmem' hMdegree
 exact grouped_resultant_power_dvd_of_primary_pieces_modMax
   primeIdeal factor multiplicity hprime hfactor hfactorMonic
     P₀ Q₀ m n P Q hPmap hQmap hPcap hQcap hresultant C hmod
end
end ProximityPrize.SubmissionLower.RCN143
end PackedLegacy_EP

/-! Packed from ProximityPrize.SubmissionLower.FN. -/
section PackedLegacy_FN
namespace ProximityPrize.SubmissionLower.RCN232
open RCN225 RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type} [CommRing R] [IsLocalRing R]
def polynomialRelationBar (surface:Polynomial R)
   (relation:Ideal (Polynomial R)):Ideal (SurfaceQuotient surface):=
 Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation
@[implicit_reducible] noncomputable def polynomialSurfaceAtPrimeAlgebra
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   Algebra R (Localization.AtPrime (polynomialRelationBar surface relation)):=
 (((algebraMap (SurfaceQuotient surface)
     (Localization.AtPrime (polynomialRelationBar surface relation))).comp
   (Ideal.Quotient.mk (Ideal.span {surface}))).comp
     (Polynomial.C:R →+*Polynomial R)).toAlgebra' (fun _ _ => mul_comm _ _)
theorem polynomialSurfaceAtPrimeAlgebra_eq_natural
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (inferInstance:Algebra R
     (Localization.AtPrime (polynomialRelationBar surface relation)))=
       polynomialSurfaceAtPrimeAlgebra surface relation:=by
 apply Algebra.algebra_ext
 intro r
 rfl
theorem polynomialSurfaceAtPrimeAlgebra_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:=polynomialSurfaceAtPrimeAlgebra surface relation
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 let quotientMap:Polynomial R →+*S:=Ideal.Quotient.mk I
 letI:=polynomialSurfaceAtPrimeAlgebra surface relation
 refine ⟨fun r hrUnit => ?_⟩
 by_contra hrNonunit
 have hrMax:r∈IsLocalRing.maximalIdeal R:=
   (IsLocalRing.mem_maximalIdeal r).2 hrNonunit
 have hrRelation:Polynomial.C r∈relation:=by
   have:r∈relation.comap (Polynomial.C:R →+*Polynomial R):=
     hcontract.symm ▸ hrMax
   exact this
 have hrBar:quotientMap (Polynomial.C r)∈bar:=
   Ideal.mem_map_of_mem quotientMap hrRelation
 have hrTarget:algebraMap S L (quotientMap (Polynomial.C r))∈
     IsLocalRing.maximalIdeal L:=by
   rw [←IsLocalization.AtPrime.map_eq_maximalIdeal bar L]
   exact Ideal.mem_map_of_mem (algebraMap S L) hrBar
 have hscalar:algebraMap R L r=
     algebraMap S L (quotientMap (Polynomial.C r)):=rfl
 have:algebraMap R L r∈IsLocalRing.maximalIdeal L:=hscalar ▸ hrTarget
 exact (IsLocalRing.mem_maximalIdeal (algebraMap R L r)).mp this hrUnit
theorem polynomialSurfaceAtPrimeNatural_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let L:=Localization.AtPrime (polynomialRelationBar surface relation)
 let natural:Algebra R L:=inferInstance
 let custom:Algebra R L:=polynomialSurfaceAtPrimeAlgebra surface relation
 have halg:natural=custom:=
   polynomialSurfaceAtPrimeAlgebra_eq_natural surface relation
 have hcustom:IsLocalHom (@algebraMap R L _ _ custom):=by
   letI:Algebra R L:=custom
   exact polynomialSurfaceAtPrimeAlgebra_isLocalHom surface relation hcontract
 change IsLocalHom (@algebraMap R L _ _ natural)
 have hmap:@algebraMap R L _ _ natural=@algebraMap R L _ _ custom:=
   congrArg (fun A:Algebra R L => @algebraMap R L _ _ A) halg
 rw [hmap]
 exact hcustom
noncomputable def polynomialSurfaceResidueEquiv
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (Polynomial R ⧸ relation) ≃+*
     IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 have hIJ:I ≤ relation:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 exact (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm.trans
   (IsLocalization.AtPrime.equivQuotMaximalIdeal bar L)
theorem polynomialSurfaceResidueEquiv_compatible
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   let aRelation:=relationResidueAlgebra relation hcontract
   letI:Algebra (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation):=aRelation
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   (algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)))).comp
       (RingEquiv.refl (IsLocalRing.ResidueField R)).toRingHom=
     (polynomialSurfaceResidueEquiv surface relation hsurface).toRingHom.comp
       (algebraMap (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R L):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 apply RingHom.ext
 intro z
 obtain ⟨r,rfl⟩:=IsLocalRing.residue_surjective z
 change algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L) (IsLocalRing.residue R r)=
   polynomialSurfaceResidueEquiv surface relation hsurface
     (algebraMap (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation) (IsLocalRing.residue R r))
 rw [IsLocalRing.ResidueField.algebraMap_residue]
 have hIJ:I ≤ relation:=
   Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 let eDouble:(S ⧸ bar) ≃+*(Polynomial R ⧸ relation):=
   DoubleQuot.quotQuotEquivQuotOfLE hIJ
 let eLocal:(S ⧸ bar) ≃+*IsLocalRing.ResidueField L:=
   IsLocalization.AtPrime.equivQuotMaximalIdeal bar L
 change IsLocalRing.residue L (algebraMap R L r)=
   eLocal (eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r)))
 have hpre:eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r))=
     Ideal.Quotient.mk bar (Ideal.Quotient.mk I (Polynomial.C r)):=by
   change (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm
     (Ideal.Quotient.mk relation (Polynomial.C r))=
       DoubleQuot.quotQuotMk I relation (Polynomial.C r)
   exact DoubleQuot.quotQuotEquivQuotOfLE_symm_mk _ hIJ
 rw [hpre]
 rfl
theorem polynomialSurfaceResidue_finite
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]
   (hfinite:
     letI:=relationResidueAlgebra relation hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation)):
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:FiniteDimensional (IsLocalRing.ResidueField R)
     (Polynomial R ⧸ relation):=hfinite
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact Module.Finite.of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)
theorem polynomialSurfaceResidue_finrank_eq_relation
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
     relationResidueAlgebra relation hcontract
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField
         (Localization.AtPrime (polynomialRelationBar surface relation)))=
     Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)).symm
end
end ProximityPrize.SubmissionLower.RCN232
end PackedLegacy_FN

/-! Packed from ProximityPrize.SubmissionLower.EB. -/
section PackedLegacy_EB
namespace ProximityPrize.SubmissionLower.RCN110
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN102 RCN106 RCN107 RCN232 RCN197 RCN192 RCN111 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hfinite in
theorem indexedNaturalSurfaceLocal_isLocalHom
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 letI:(polynomialRelationBar (indexedFiberSurface q hq surface)
     (indexedFiberRelation component lam mu nu order ht q hq a)).IsMaximal:=by
   change (indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal
   exact hbarMax
 exact polynomialSurfaceAtPrimeNatural_isLocalHom
   (indexedFiberSurface q hq surface)
   (indexedFiberRelation component lam mu nu order ht q hq a)
   (indexedFiberRelation_comap_C_eq_maximalIdeal
     component lam mu nu order ht hfinite q hq a)
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finite
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   have hrelFinite:=localizedRelationResidue_finite Omega L order e
     (ht a) (hfinite a) (hgen a)
   exact polynomialSurfaceResidue_finite P J hcontract hsurfaceJ hrelFinite
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finrank_eq_plane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
     indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let R:=LocalCoefficient Omega L order e (ht a) (hfinite a)
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar P J))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom P J hcontract
   let aRelation:=relationResidueAlgebra J hcontract
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation
   letI:SMul (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation.toSMul
   let targetSemiring:Semiring (Polynomial R ⧸ J):=inferInstance
   letI:AddCommMonoid (Polynomial R ⧸ J):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=Algebra.toModule
   calc
     Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField (Localization.AtPrime
           (polynomialRelationBar P J)))=
       Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
         polynomialSurfaceResidue_finrank_eq_relation P J hcontract hsurfaceJ
     _=indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
       simpa [indexedPlaneResidueWeight] using
         localizedRelationResidue_finrank_eq_unlocalized Omega L order e
           (ht a) (hfinite a) (hgen a)
end
end ProximityPrize.SubmissionLower.RCN110
end PackedLegacy_EB

/-! Packed from ProximityPrize.SubmissionLower.EA. -/
section PackedLegacy_EA
namespace ProximityPrize.SubmissionLower.RCN109
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN102 RCN106 RCN107 RCN143 RCN307 RCN014 RCN120 RCN236 RCN110 RCN111
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*Module.finrank
       (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))))∣
     Polynomial.resultant surface tail m n:=by
 letI:DecidableEq (RatFunc Omega):=Classical.decEq _
 letI:(Ideal.span {q}).IsPrime:=
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 let weight:IndexedFactorFiber component lam mu nu order ht q → ℕ:=fun a =>
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))
 let cert:=indexedWeightedFiberPrimaryPieces component hcomponent lam mu nu
   order ht hfinite hgen q hq surface tail hbarne multiplicity htail
     (hlocal:=hlocal) (hresfinite:=hresfinite)
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.Finite (FiberCoefficient q hq)
       (Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=fun a => by
   obtain ⟨M,hMmonic,hMmem⟩:=exists_monic_mem_indexedFiberRelation
     component lam mu nu order ht hfinite hgen q hq a
   apply RCN309.moduleFinite_quotient_of_monic_mem
     (cert.pieces a) (M^multiplicity a) (hMmonic.pow _)
   have hpow:M^multiplicity a∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a:=
     (show indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a ≤
         Ideal.span {indexedFiberSurface q hq surface} ⊔
           indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a
       from le_sup_right) (Ideal.pow_mem_pow hMmem (multiplicity a))
   simpa [cert,indexedWeightedFiberPrimaryPieces,
     primaryPiecesCertificateOfMembershipWeighted,mappedPrimaryPiece] using hpow
 letI:Module.Finite (FiberCoefficient q hq)
     (∀ a,Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=inferInstance
 exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   (Ideal.span {q}) q (fun a => multiplicity a*weight a)
     rfl hq hqMonic surface tail m n
     (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
     rfl rfl hPcap hQcap hresultant hPbar cert
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*indexedPlaneResidueWeight component lam mu nu order
       ht hfinite a.1)∣Polynomial.resultant surface tail m n:=by
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=
   fun a => indexedFiberRelationBar_isMaximal component lam mu nu order ht
     hfinite hgen q hq surface hsurface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht
     hfinite q hq surface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceResidue_finite component lam mu nu order ht
     hfinite hgen q hq surface a (hsurface a)
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd component hcomponent
   lam mu nu order ht hfinite hgen q hq hqMonic surface tail m n hbarne
     multiplicity htail hPcap hQcap hresultant hPbar
 have hweight:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
   fun a => indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu
     order ht hfinite hgen q hq surface a (hsurface a)
 simpa only [hweight] using hpow
end
end ProximityPrize.SubmissionLower.RCN109
end PackedLegacy_EA

/-! Packed from ProximityPrize.SubmissionLower.M1. -/
section PackedLegacy_M1
namespace ProximityPrize.SubmissionLower.RCN195
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_surface_residue_ne_zero
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (P₀:Polynomial (Polynomial (RatFunc K)))
   (hspecial:P₀.map
     (AdjoinRoot.mk (projectedFactor K L order e ht))≠0):
   (P₀.map (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))).map
       (IsLocalRing.residue (LocalCoefficient K L order e ht hfinite))≠0:=by
 let q:=projectedFactor K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let E:=Rp ⧸ IsLocalRing.maximalIdeal Rp
 let eqv:=coefficientResidueEquiv K L order e ht hfinite
 let source:Polynomial (AdjoinRoot q):=P₀.map (AdjoinRoot.mk q)
 let target:Polynomial E:=
   (P₀.map (algebraMap (Polynomial (RatFunc K)) Rp)).map
     (IsLocalRing.residue Rp)
 have hmap:source.map eqv.toRingHom=target:=by
   apply Polynomial.ext
   intro n
   simp only [source,target,Polynomial.coeff_map,Function.comp_apply]
   exact coefficientResidueEquiv_mk K L order e ht hfinite (P₀.coeff n)
 intro hzero
 apply hspecial
 apply (Polynomial.map_injective eqv.toRingHom eqv.injective)
 have htargetZero:target=0:=hzero
 rw [hmap,htargetZero,Polynomial.map_zero]
end
end ProximityPrize.SubmissionLower.RCN195
end PackedLegacy_M1

/-! Packed from ProximityPrize.SubmissionLower.E2. -/
section PackedLegacy_E2
namespace ProximityPrize.SubmissionLower.RCN251
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN245 RCN246 RCN247 RCN249 RCN102 RCN103 RCN106 RCN107 RCN108 RCN109 RCN195 RCN120 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN251.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN251.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
 (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
end
end ProximityPrize.SubmissionLower.RCN251
end PackedLegacy_E2

/-! Packed from ProximityPrize.SubmissionLower.N3. -/
section PackedLegacy_N3
namespace ProximityPrize.SubmissionLower.RCN255
open RCN135 RCN136 RCN244 RCN249 RCN245 RCN106 RCN103 RCN093 RCN095 RCN125 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem planeSurface_map_adjoinRoot_ne_zero
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega) (hirr:Irreducible surface)
   (hpositive:0 < surface.natDegree):
   surface.map (AdjoinRoot.mk q)≠0:=by
 letI:Fact (Irreducible q):=⟨hq⟩
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap (RatFunc Omega) (AdjoinRoot q))
       (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
 have hs:=RCN360.bimap_specialization_ne_zero
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.bimap_specialization,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN255.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN255.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
def StageFamilySurfaceSpecializationNonzero
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):Prop:=
 (stageSurfacePlane S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem stageFamily_surface_specialization_ne
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
   StageFamilySurfaceSpecializationNonzero S F q:=by
 change (planeMap (GenericField K) F.order
   (flagAlgHom F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
 exact planeSurface_map_adjoinRoot_ne_zero q hq
   (planeMap (GenericField K) F.order (flagAlgHom F.lam F.mu F.nu S.G))
   (transformedSurface_irreducible F.lam F.mu F.nu F.order S.irreducible_G
     (F.component a.1) (F.ht a.1)) F.positive
end
end ProximityPrize.SubmissionLower.RCN255
end PackedLegacy_N3

/-! Packed from ProximityPrize.SubmissionLower.C4. -/
section PackedLegacy_C4
namespace ProximityPrize.SubmissionLower.RCN112
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN103 RCN012 RCN011 RCN264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
local instance _root_.ProximityPrize.SubmissionLower.RCN112.instDecidableEqRatFunc_proximityPrize :DecidableEq (RatFunc Omega):=Classical.decEq _
variable {G T H:MvPolynomial (Fin 3) Omega}
def flagPlaneResultant (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (G T:MvPolynomial (Fin 3) Omega):Polynomial (RatFunc Omega):=
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 Polynomial.resultant P Q P.natDegree Q.natDegree
theorem flagPlaneResultant_ne
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (ht:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hpositive:0 < (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree):
   flagPlaneResultant lam mu nu order G T≠0:=by
 exact RCN362.irreducible_resultant_ne_zero_of_not_dvd
   (planeMap Omega order (flagAlgHom lam mu nu G))
   (planeMap Omega order (flagAlgHom lam mu nu T))
   (transformedSurface_irreducible lam mu nu order hG C ht) hpositive
   (transformedSurface_not_dvd_tail lam mu nu order hG hproper C ht)
theorem flagPlaneResultant_z_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu zOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega zOrder (flagAlgHom lam mu nu G))
   (planeMap Omega zOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega zOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all (surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.yz+tailFlag.all) (flagMixed surfaceFlag tailFlag unitZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.zOuter tCaps.zOuter
   gCaps.zTotal tCaps.zTotal (z_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_u_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu uOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitYZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega uOrder (flagAlgHom lam mu nu G))
   (planeMap Omega uOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega uOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitYZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.uOuter tCaps.uOuter
   gCaps.uTotal tCaps.uTotal (u_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_v_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu vOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitAllFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega vOrder (flagAlgHom lam mu nu G))
   (planeMap Omega vOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega vOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   (surfaceFlag.yz+surfaceFlag.all) (tailFlag.yz+tailFlag.all)
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitAllFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.vOuter tCaps.vOuter
   gCaps.vTotal tCaps.vTotal (v_flag_trapezoid_budget surfaceFlag tailFlag)
end
end ProximityPrize.SubmissionLower.RCN112
end PackedLegacy_C4

/-! Packed from ProximityPrize.SubmissionLower.N2. -/
section PackedLegacy_N2
namespace ProximityPrize.SubmissionLower.RCN254
open RCN135 RCN136 RCN086 RCN244 RCN245 RCN249 RCN112 RCN103 RCN113 RCN093 RCN095 RCN011
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN254.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN254.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
end
end ProximityPrize.SubmissionLower.RCN254
end PackedLegacy_N2

/-! Packed from ProximityPrize.SubmissionLower.FZ. -/
section PackedLegacy_FZ
namespace ProximityPrize.SubmissionLower.RCN250
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN245 RCN249 RCN251 RCN254 RCN102 RCN106 RCN107 RCN109 RCN120 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN250.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN250.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
def StageFamilySurfaceModNonzero
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):Prop:=
 (indexedFiberSurface W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
     (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0
end
end ProximityPrize.SubmissionLower.RCN250
end PackedLegacy_FZ

/-! Packed from ProximityPrize.SubmissionLower.N0. -/
section PackedLegacy_N0
namespace ProximityPrize.SubmissionLower.RCN252
open RCN135 RCN136 RCN074 RCN244 RCN249 RCN245 RCN106 RCN107 RCN108 RCN103 RCN102 RCN195 RCN255 RCN250 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN252.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN252.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W:=by
 rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 have hspecial:=stageFamily_surface_specialization_ne S F q hq
   (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
 change surface.map (AdjoinRoot.mk q)≠0 at hspecial
 change (indexedFiberSurface q hq surface).map
   (IsLocalRing.residue (FiberCoefficient q hq))≠0
 subst q
 exact localized_surface_residue_ne_zero (GenericField K)
   (CoordinateField (GenericField K) (F.component a).1) F.order
   (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
   (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.RCN252
end PackedLegacy_N0

/-! Packed from ProximityPrize.SubmissionLower.N1. -/

/-! Packed from ProximityPrize.SubmissionLower.Q0. -/
section PackedLegacy_Q0
namespace ProximityPrize.SubmissionLower.RCN333
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN249 RCN251 RCN252 RCN255 RCN250 RCN247 RCN245 RCN106 RCN107 RCN108 RCN102 RCN103 RCN109 RCN112 RCN113 RCN264 RCN120 RCN243 RCN111 RCN093 RCN095 RCN125 RCN066 RCN336 RCN226 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN333.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN333.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem finiteDimensional_coordinateField_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega Q):=by
 subst Q
 exact hfinite
theorem flagGenerators_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hgen:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 1))} :
         Set (CoordinateField Omega P)) = ⊤) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 2)),
       flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 1))} :
       Set (CoordinateField Omega Q)) = ⊤:=by
 subst Q
 exact hgen
theorem indexedComponentFactor_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   projectedFactor Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   projectedFactor Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem relationKernel_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   relationKernel Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   relationKernel Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem flagPlaneMap_mem_relation
   {Omega:Type} [Field Omega]
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A:MvPolynomial (Fin 3) Omega} (hA:A ∈ P) :
   flagPlaneMap Omega lam mu nu order A ∈
     relationKernel Omega (CoordinateField Omega P) order
       (flagEvaluation Omega P lam mu nu) ht:=by
 change planeEvaluation Omega (CoordinateField Omega P) order
   (flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom lam mu nu A)) = 0
 rw [← RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation Omega P lam mu nu (flagAlgHom lam mu nu A) = 0
 rw [flagEvaluation_flag]
 change A ∈ RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rw [coordinateEvaluation_ker]
 exact hA
theorem ideal_mem_right_of_sub_mem
   {R:Type} [CommRing R] (P:Ideal R) {A B:R}
   (hA:A ∈ P) (hAB:A - B ∈ P):B ∈ P:=by
 have h:=P.sub_mem hA hAB
 simpa only [sub_sub_cancel] using h
@[simp] theorem flagPlaneMap_apply
   {Omega:Type} [Field Omega] (lam mu nu:Omega)
   (order:Fin 3 ≃ Fin 3) (A:MvPolynomial (Fin 3) Omega) :
   flagPlaneMap Omega lam mu nu order A =
     planeMap Omega order (flagAlgHom lam mu nu A):=rfl
theorem reducedStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1) - Tred)
   {A:Type} [Fintype A]
   (component:A → RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F))
   (hcomponent:Function.Injective component)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (component a).1)) = ⊤)
   (positive:0 < (stageSurfacePlane S lam mu nu order).natDegree)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (hqMonic:q.Monic)
   (a0:IndexedFactorFiber component lam mu nu order ht q) :
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) *
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1) ∣
     flagPlaneResultant lam mu nu order S.G Tred:=by
 let e:=regularComponentEquiv
   (H:=regularitySurface (polynomialEmbedding K) S.F) hd
 let oldComponent:A → StageComponent S:=fun a => e.symm (component a)
 have oldComponent_val (a:A):(oldComponent a).1 = (component a).1 :=
   regularComponentEquiv_symm_val hd (component a)
 have holdInjective:Function.Injective oldComponent :=
   e.symm.injective.comp hcomponent
 have htold:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
       (MvPolynomial.X (order 0))):=by
   intro a
   rw [oldComponent_val a]
   exact ht a
 have hfiniteold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (oldComponent a).1):=by
   intro a
   exact finiteDimensional_coordinateField_congr
     (oldComponent_val a).symm lam mu nu order (ht a) (htold a) (hfinite a)
 have hgenold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (oldComponent a).1)) = ⊤:=by
   intro a
   exact flagGenerators_congr (oldComponent_val a).symm lam mu nu order
     (ht a) (htold a) (hgen a)
 let surface:=stageSurfacePlane S lam mu nu order
 let oldTail:=stageTailPlane S lam mu nu order
 let redTail:=flagPlaneMap (GenericField K) lam mu nu order Tred
 letI:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime:=by
   exact indexedFiberSurface_span_isPrime component lam mu nu order ht
     S.irreducible_G q hq a0
 have hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   change flagPlaneMap (GenericField K) lam mu nu order S.G ∈ _
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_G_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hfirstProper
   have hsum:=hd.add hr
   simpa only [sub_add_cancel] using hsum
 have hredTailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     redTail ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_T_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperLocal:indexedFiberTail q hq redTail ∉
     Ideal.span {indexedFiberSurface q hq surface}:=by
   exact indexedFiberTail_not_mem_surface component lam mu nu order ht
     S.irreducible_G hproperRed q hq a0
 have hbar:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥:=by
   intro a
   exact indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq
     surface redTail hredTailRoot hproperLocal a
 have hplaneDvd:surface ∣ oldTail-redTail:=by
   simpa only [surface,oldTail,redTail,stageSurfacePlane,stageTailPlane,
     map_sub] using map_dvd (flagPlaneMap (GenericField K) lam mu nu order) hd
 have htail:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberTail q hq redTail ∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a ^
           transportedMultiplicity hd
             (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
             (component a.1):=by
   intro a
   let Q:=Ideal.span {indexedFiberSurface q hq surface} ⊔
     indexedFiberRelation component lam mu nu order ht q hq a ^
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1)
   have hfactorOld:q =
       indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a.1:=a.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a.1).symm
           lam mu nu order (ht a.1) (htold a.1)
   let aold:IndexedFactorFiber oldComponent lam mu nu order htold q :=
     ⟨a.1,hfactorOld⟩
   have hold:=indexedFiberTail_mem_primary S hfirstProper oldComponent
     lam mu nu order htold hfiniteold hgenold q hq aold
   have aold_val:aold.1 = a.1:=rfl
   have hcomponentVal:(oldComponent aold.1).1 = (component a.1).1:=by
     rw [aold_val,oldComponent_val]
   have hrel:indexedFiberRelation oldComponent lam mu nu order htold q hq aold =
       indexedFiberRelation component lam mu nu order ht q hq a:=by
     unfold indexedFiberRelation
     exact congrArg (Ideal.map (fiberLocalizePlane q hq))
       (relationKernel_congr hcomponentVal lam mu nu order
         (htold aold.1) (ht a.1))
   have hmult:localMultiplicity S
       (canonicalLocalDVRFamily S hfirstProper) (oldComponent aold.1) =
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1):=by
     change localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component aold.1)) =
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component a.1))
     rw [aold_val]
   rw [hrel,hmult] at hold
   have holdQ:indexedFiberTail q hq oldTail ∈ Q:=by
     simpa only [oldTail,surface,Q] using hold
   have hfiberDvd:indexedFiberSurface q hq surface ∣
       indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail:=by
     simpa only [indexedFiberSurface,indexedFiberTail,map_sub] using
       map_dvd (fiberLocalizePlane q hq) hplaneDvd
   have hdiff:indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail ∈ Q :=
     (show Ideal.span {indexedFiberSurface q hq surface} ≤ Q from le_sup_left)
       (Ideal.mem_span_singleton.mpr hfiberDvd)
   exact ideal_mem_right_of_sub_mem Q
     (A:=indexedFiberTail q hq oldTail)
     (B:=indexedFiberTail q hq redTail) holdQ hdiff
 have hresultant0:=flagPlaneResultant_ne lam mu nu order
   S.irreducible_G hproperRed (component a0.1) (ht a0.1) positive
 have hresultant:Polynomial.resultant surface redTail surface.natDegree
     redTail.natDegree ≠ 0:=by
   simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
     flagPlaneMap_apply] using hresultant0
 have hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0:=by
   have hfactorA0old:q =
       indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a0.1:=a0.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a0.1).symm
           lam mu nu order (ht a0.1) (htold a0.1)
   let F:StageIndexedFlagFamily S A:={
     component:=oldComponent
     injective:=holdInjective
     lam:=lam
     mu:=mu
     nu:=nu
     order:=order
     ht:=htold
     finite:=hfiniteold
     generates:=hgenold
     positive:=positive }
   let a0old:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q :=
     ⟨a0.1,hfactorA0old⟩
   let W:StageIndexedFactor S A F :=
     { q:=q, irreducible:=hq, monic:=hqMonic, witness:=a0old }
   have hPbar0:=stageFamily_surface_mod_ne S F W
   change (indexedFiberSurface q hq
     (stageSurfacePlane S lam mu nu order)).map
       (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 at hPbar0
   simpa only [surface] using hPbar0
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   component hcomponent lam mu nu order ht hfinite hgen q hq hqMonic
   surface redTail surface.natDegree redTail.natDegree hsurface hbar
   (fun a => transportedMultiplicity hd
     (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
     (component a.1)) htail Polynomial.natDegree_map_le
       Polynomial.natDegree_map_le hresultant hPbar
 simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
   flagPlaneMap_apply] using hpow
end
end ProximityPrize.SubmissionLower.RCN333
end PackedLegacy_Q0

/-! Packed from ProximityPrize.SubmissionLower.A1. -/
section PackedLegacy_A1
namespace ProximityPrize.SubmissionLower.RCN031
open RCN002 RCN264 RCN341 RCN037 RCN038 RCN093 RCN125 RCN116 RCN120 RCN021 RCN022
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
abbrev ActiveNestedZIndex:={C:RegularComponent Omega G T H//
 Transcendental Omega (coordinate Omega C.1 2)}
def activeNestedZComponent:ActiveNestedZIndex (G:=G) (T:=T) (H:=H) →
   RegularComponent Omega G T H:=Subtype.val
theorem activeNestedZComponent_injective:Function.Injective
   (activeNestedZComponent (G:=G) (T:=T) (H:=H)):=
 Subtype.val_injective
def activeNestedZTranscendental
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0))):=by
 simpa [zOrder,Equiv.swap_apply_def] using a.2
def activeNestedUTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0))):=by
 simpa [uOrder] using D.uTranscendental C
def activeNestedVTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0))):=by
 simpa [vOrder,Equiv.swap_apply_def] using D.allAffineTranscendental C
include hZ in
theorem activeNestedZGate
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H))
   (hx:Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0)))):
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1)):=by
 have hx':Transcendental Omega (coordinate Omega a.1.1 2):=by
   simpa [zOrder,Equiv.swap_apply_def] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1))
 rw [hemb]
 exact hZ a.1 hx'
theorem activeNestedUGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hx':Transcendental Omega (affineU Omega C.1 D.lam):=by
   simpa [uOrder] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact D.uGate C hx'
theorem activeNestedVGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hemb:=elementEmbedding_congr hx (D.allAffineTranscendental C)
   (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact ⟨D.allFinite C,D.allSeparable C⟩
def activeNestedZFinite (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):=
 (activeNestedZGate base hactive hZ hSderiv D a
   (activeNestedZTranscendental base hactive hSderiv D a)).1
def activeNestedUFinite (C:RegularComponent Omega G T H):=
 (activeNestedUGate base hactive hSderiv D C
   (activeNestedUTranscendental base hactive hSderiv D C)).1
def activeNestedVFinite (C:RegularComponent Omega G T H):=
 (activeNestedVGate base hactive hSderiv D C
   (activeNestedVTranscendental base hactive hSderiv D C)).1
theorem activeNestedZGenerates
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam)
     zOrder (activeNestedZTranscendental base hactive hSderiv D a)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 1))}:
       Set (CoordinateField Omega a.1.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1)
       (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 0)))
       (activeNestedZTranscendental base hactive hSderiv D a)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 1))}:Set (CoordinateField Omega a.1.1))=⊤)
 rw [hemb]
 simpa [zOrder,Equiv.swap_apply_def] using flag_generators_z Omega a.1.1 D.lam D.mu
   (D.mu*D.lam) a.2
theorem activeNestedUGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     uOrder (activeNestedUTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 0)))
       (activeNestedUTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [uOrder] using flag_generators_u Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.uTranscendental C)
theorem activeNestedVGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     vOrder (activeNestedVTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 0)))
       (activeNestedVTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [vOrder,Equiv.swap_apply_def] using flag_generators_v Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.allAffineTranscendental C)
end
end ProximityPrize.SubmissionLower.RCN031
end PackedLegacy_A1

/-! Packed from ProximityPrize.SubmissionLower.A0. -/
section PackedLegacy_A0
namespace ProximityPrize.SubmissionLower.RCN029
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN125 RCN031 RCN106 RCN111 RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (multiplicity:RegularComponent Omega G T H → ℕ)
def ActiveNestedZFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (a₀:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q),
   q^(∑ a:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q,
     multiplicity a.1.1*indexedPlaneResidueWeight
       (activeNestedZComponent (G:=G) (T:=T) (H:=H))
       D.lam D.mu (D.mu*D.lam) zOrder
       (activeNestedZTranscendental base hactive hSderiv D)
       (activeNestedZFinite base hactive hZ hSderiv D) a.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T
def ActiveNestedUFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) uOrder
       (activeNestedUTranscendental base hactive hSderiv D)
       (activeNestedUFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T
def ActiveNestedVFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) vOrder
       (activeNestedVTranscendental base hactive hSderiv D)
       (activeNestedVFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T
structure ActiveNestedFixedPowers:Prop where
 z:ActiveNestedZFixedPowers base hactive hZ hSderiv D multiplicity
 u:ActiveNestedUFixedPowers base hactive hSderiv D multiplicity
 v:ActiveNestedVFixedPowers base hactive hSderiv D multiplicity
end
end ProximityPrize.SubmissionLower.RCN029
end PackedLegacy_A0

/-! Packed from ProximityPrize.SubmissionLower.P8. -/
section PackedLegacy_P8
namespace ProximityPrize.SubmissionLower.RCN331
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN243 RCN264 RCN095 RCN066 RCN336 RCN333 RCN029 RCN031 RCN037 RCN038 RCN341 RCN117 RCN125 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN331.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN331.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem reducedStage_activeFixedPowers
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1) - Tred)
   (base:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 0) ≠ 0 ∨
       KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 2) ≠ 0)
   (hZ:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G ≠ 0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv) :
   ActiveNestedFixedPowers base hactive hZ hSderiv D
     (transportedMultiplicity hd
       (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))):=by
 refine { z:=?_, u:=?_, v:=?_ }
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (activeNestedZComponent (G:=S.G) (T:=Tred)
       (H:=regularitySurface (polynomialEmbedding K) S.F))
     activeNestedZComponent_injective D.lam D.mu (D.mu * D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D)
     (activeNestedZFinite base hactive hZ hSderiv D)
     (activeNestedZGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D)
     (activeNestedUFinite base hactive hSderiv D)
     (activeNestedUGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D)
     (activeNestedVFinite base hactive hSderiv D)
     (activeNestedVGenerates base hactive hSderiv D)
     (flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional)
     q hq hqMonic a0
end
end ProximityPrize.SubmissionLower.RCN331
end PackedLegacy_P8

/-! Packed from ProximityPrize.SubmissionLower.DJ. -/
section PackedLegacy_DJ
namespace ProximityPrize.SubmissionLower.RCN030
open RCN002 RCN264 RCN341 RCN042 RCN344 RCN037 RCN038 RCN040 RCN046 RCN237 RCN095 RCN093 RCN125 RCN116 RCN022 RCN031
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
noncomputable def activeNestedUnitFamily:
   AdaptiveUnitProjectionFamily base surfaceFlag tailFlag:=
 adaptiveUnitProjectionFamily_of_active_nested surfaceFlag tailFlag base hactive
   hZ hSderiv D hG hproper hGsupport hTsupport
theorem activeNestedUnitFamily_zCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=rfl
theorem activeNestedUnitFamily_uCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)):=rfl
theorem activeNestedUnitFamily_allCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (Sum.inr {
         embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
           (affineV Omega C.1 D.mu (D.mu*D.lam))
             (D.allAffineTranscendental C)
         finite:=D.allFinite C
         separable:=D.allSeparable C}):=rfl
theorem activeNestedUnitFamily_zCost_eq_flagCost
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost a.1=
     coordinateDegree Omega (CoordinateField Omega a.1.1)
       (coordinateOfGate
         (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (zOrder 0)))
         (activeNestedZGate base hactive hZ hSderiv D a)):=by
 rw [activeNestedUnitFamily_zCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ a.2]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedZTranscendental base hactive hSderiv D a)]
 rw [elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])]
theorem activeNestedUnitFamily_uCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (uOrder 0)))
         (activeNestedUGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_uCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ (D.uTranscendental C)]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedUTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])]
theorem activeNestedUnitFamily_allCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (vOrder 0)))
         (activeNestedVGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_allCost]
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
         (D.allAffineTranscendental C)).toRingHom.toAlgebra;
   Module.finrank (RatFunc Omega) (CoordinateField Omega C.1))=_
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedVTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])]
end
end ProximityPrize.SubmissionLower.RCN030
end PackedLegacy_DJ

/-! Packed from ProximityPrize.SubmissionLower.K2. -/
section PackedLegacy_K2
namespace ProximityPrize.SubmissionLower.RCN105
open RCN002 RCN011 RCN264 RCN093 RCN120 RCN042 RCN344 RCN106 RCN111 RCN226 RCN113 RCN021 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type}
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
theorem indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (a:A):
   coordinateDegree Omega (CoordinateField Omega (component a).1)
     (coordinateOfGate
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0)))
       (hgate a))=
     (indexedComponentFactor component lam mu nu order ht a).natDegree*
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
 rw [coordinateOfGate_degree_of_transcendental _ (hgate a) (ht a)]
 let F:=RatFunc Omega
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Algebra F L:=flagBaseAlgebra Omega (component a).1
   lam mu nu order (ht a)
 letI:FiniteDimensional F L:=hfinite a
 letI:J.IsMaximal:=relationKernel_isMaximal Omega L order e (ht a)
   (hfinite a) (hgen a)
 let aResidue:=residueAlgebra q J
   (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 have hq:Irreducible q:=projectedFactor_irreducible Omega L order e
   (ht a) (hfinite a)
 let phi:PlaneRing Omega →ₐ[F] L:={
   toRingHom:=planeEvaluation Omega L order e (ht a)
   commutes':=fun c => by
     change planeEvaluation Omega L order e (ht a)
       (Polynomial.C (Polynomial.C c))=algebraMap F L c
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) (hgen a)
 let eqv:(PlaneRing Omega ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing Omega ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 have hquot:Module.finrank F (PlaneRing Omega ⧸ J)=
     Module.finrank F L:=eqv.toLinearEquiv.finrank_eq
 change Module.finrank F L=q.natDegree*
   indexedPlaneResidueWeight component lam mu nu order ht hfinite a
 rw [show indexedPlaneResidueWeight component lam mu nu order ht hfinite a=
     Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J) by rfl]
 calc
   Module.finrank F L=Module.finrank F (PlaneRing Omega ⧸ J):=hquot.symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J):=
     quotient_finrank_eq_natDegree_mul_residue_finrank q hq J
       (relationKernel_comap_C Omega L order e (ht a))
end
end ProximityPrize.SubmissionLower.RCN105
end PackedLegacy_K2

/-! Packed from ProximityPrize.SubmissionLower.AN. -/
section PackedLegacy_AN
namespace ProximityPrize.SubmissionLower.RCN343
open scoped Classical BigOperators
open RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Base:Type} [Field Base] [DecidableEq Base]
structure WeightedGroupedResultantChannel
   {I:Type*} [Fintype I]
   (multiplicity cost:I → ℕ) (budget:ℕ) where
 resultant:Polynomial Base
 factor:I → Polynomial Base
 residueWeight:I → ℕ
 resultant_ne:resultant≠0
 factor_irreducible:∀ i,Irreducible (factor i)
 factor_monic:∀ i,(factor i).Monic
 groupedPowerDvd:∀ f∈Finset.univ.image factor,
   f^(∑ i with factor i=f,multiplicity i*residueWeight i)∣resultant
 cost_le_residue_mul_degree:∀ i,
   cost i ≤ residueWeight i*(factor i).natDegree
 resultant_degree_le:resultant.natDegree ≤ budget
theorem WeightedGroupedResultantChannel.sum_mul_cost_le
   {I:Type*} [Fintype I]
   {multiplicity cost:I → ℕ} {budget:ℕ}
   (C:WeightedGroupedResultantChannel
     (Base:=Base) multiplicity cost budget):
   (∑ i,multiplicity i*cost i) ≤ budget:=by
 let weightedMultiplicity:I → ℕ:=fun i↦
   multiplicity i*C.residueWeight i
 have hfactor:=sum_grouped_power_factor_degrees_le
   C.resultant C.factor weightedMultiplicity C.resultant_ne
     C.factor_irreducible C.factor_monic C.groupedPowerDvd
 calc
   (∑ i,multiplicity i*cost i) ≤
       ∑ i,multiplicity i*
         (C.residueWeight i*(C.factor i).natDegree):=
     Finset.sum_le_sum (fun i _↦
       Nat.mul_le_mul_left (multiplicity i)
         (C.cost_le_residue_mul_degree i))
   _=∑ i,weightedMultiplicity i*(C.factor i).natDegree:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [weightedMultiplicity,Nat.mul_assoc]
   _ ≤ C.resultant.natDegree:=hfactor
   _ ≤ budget:=C.resultant_degree_le
end
end ProximityPrize.SubmissionLower.RCN343
end PackedLegacy_AN

/-! Packed from ProximityPrize.SubmissionLower.K1. -/
section PackedLegacy_K1
namespace ProximityPrize.SubmissionLower.RCN104
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN106 RCN111 RCN105 RCN120 RCN226 RCN042 RCN344 RCN343
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
noncomputable def indexedWeightedFlagPlaneChannel_of_fixedFactors
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (multiplicity:A → ℕ)
   (resultant:Polynomial (RatFunc Omega)) (budget:ℕ)
   (hresultant:resultant≠0)
   (hdegree:resultant.natDegree ≤ budget)
   (hfixed:∀ (q:Polynomial (RatFunc Omega))
     (hq:Irreducible q) (hqMonic:q.Monic)
     (a₀:IndexedFactorFiber component lam mu nu order ht q),
     q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
       multiplicity a.1*indexedPlaneResidueWeight component
         lam mu nu order ht hfinite a.1)∣resultant):
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     (fun a↦coordinateDegree Omega (CoordinateField Omega (component a).1)
       (coordinateOfGate
         (flagEvaluation Omega (component a).1 lam mu nu
           (MvPolynomial.X (order 0))) (hgate a))) budget:=by
 let factor:=indexedComponentFactor component lam mu nu order ht
 let weight:=indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   residueWeight:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   groupedPowerDvd:=?_
   cost_le_residue_mul_degree:=?_
   resultant_degree_le:=hdegree}
 · intro a
   exact projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,multiplicity b*weight b)=
         ∑ b:IndexedFactorFiber component lam mu nu order ht (factor a),
           multiplicity b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦multiplicity b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost:=indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
     component lam mu nu order ht hfinite hgen hgate a
   simpa only [factor,weight,Nat.mul_comm] using hcost.le
end
end ProximityPrize.SubmissionLower.RCN104
end PackedLegacy_K1

/-! Packed from ProximityPrize.SubmissionLower.Q9. -/
section PackedLegacy_Q9
namespace ProximityPrize.SubmissionLower.RCN342
open scoped Classical BigOperators
open RCN343
noncomputable section
set_option autoImplicit false
variable {Base:Type} [Field Base] [DecidableEq Base]
noncomputable def recost
   {I:Type*} [Fintype I] {multiplicity oldCost newCost:I → ℕ}
   {budget:ℕ}
   (C:WeightedGroupedResultantChannel (Base:=Base)
     multiplicity oldCost budget)
   (hcost:∀ i,newCost i ≤ oldCost i):
   WeightedGroupedResultantChannel (Base:=Base)
     multiplicity newCost budget where
 resultant:=C.resultant
 factor:=C.factor
 residueWeight:=C.residueWeight
 resultant_ne:=C.resultant_ne
 factor_irreducible:=C.factor_irreducible
 factor_monic:=C.factor_monic
 groupedPowerDvd:=C.groupedPowerDvd
 cost_le_residue_mul_degree i:=(hcost i).trans (C.cost_le_residue_mul_degree i)
 resultant_degree_le:=C.resultant_degree_le
noncomputable def emptyChannel
   {I:Type*} [Fintype I] [IsEmpty I]
   (multiplicity cost:I → ℕ) (budget:ℕ):
   WeightedGroupedResultantChannel (Base:=Base) multiplicity cost budget where
 resultant:=1
 factor i:=isEmptyElim i
 residueWeight i:=isEmptyElim i
 resultant_ne:=one_ne_zero
 factor_irreducible i:=isEmptyElim i
 factor_monic i:=isEmptyElim i
 groupedPowerDvd f hf:=by simp at hf
 cost_le_residue_mul_degree i:=isEmptyElim i
 resultant_degree_le:=by simp
end
end ProximityPrize.SubmissionLower.RCN342
end PackedLegacy_Q9

/-! Packed from ProximityPrize.SubmissionLower.DI. -/
section PackedLegacy_DI
namespace ProximityPrize.SubmissionLower.RCN028
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN095 RCN125 RCN117 RCN031 RCN030 RCN029 RCN112 RCN104 RCN343 RCN342
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedZChannel
   [Nonempty (ActiveNestedZIndex (G:=G) (T:=T) (H:=H))]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)↦multiplicity a.1)
     (fun a↦U.toPrimeFlagBudgetFamily.zCost a.1)
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let a₀:ActiveNestedZIndex (G:=G) (T:=T) (H:=H):=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) zOrder
   hG hproper a₀.1 (activeNestedZTranscendental base hactive hSderiv D a₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
 have hdeg:=flagPlaneResultant_z_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (activeNestedZComponent (G:=G) (T:=T) (H:=H))
   D.lam D.mu (D.mu*D.lam) zOrder
   (activeNestedZTranscendental base hactive hSderiv D)
   (activeNestedZFinite base hactive hZ hSderiv D)
   (activeNestedZGenerates base hactive hSderiv D)
   (activeNestedZGate base hactive hZ hSderiv D)
   (fun a↦multiplicity a.1)
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T)
   (flagMixed surfaceFlag tailFlag unitZFlag) hres hdeg powers.z
 exact recost raw fun a↦
   (activeNestedUnitFamily_zCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport a).le
noncomputable def activeNestedUChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.yzCost
     (flagMixed surfaceFlag tailFlag unitYZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) uOrder
   hG hproper C₀ (activeNestedUTranscendental base hactive hSderiv D C₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
 have hdeg:=flagPlaneResultant_u_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) uOrder
   (activeNestedUTranscendental base hactive hSderiv D)
   (activeNestedUFinite base hactive hSderiv D)
   (activeNestedUGenerates base hactive hSderiv D)
   (activeNestedUGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T)
   (flagMixed surfaceFlag tailFlag unitYZFlag) hres hdeg powers.u
 exact recost raw fun C↦
   (activeNestedUnitFamily_uCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
noncomputable def activeNestedVChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.allCost
     (flagMixed surfaceFlag tailFlag unitAllFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) vOrder
   hG hproper C₀ (activeNestedVTranscendental base hactive hSderiv D C₀)
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
 have hdeg:=flagPlaneResultant_v_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) vOrder
   (activeNestedVTranscendental base hactive hSderiv D)
   (activeNestedVFinite base hactive hSderiv D)
   (activeNestedVGenerates base hactive hSderiv D)
   (activeNestedVGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T)
   (flagMixed surfaceFlag tailFlag unitAllFlag) hres hdeg powers.v
 exact recost raw fun C↦
   (activeNestedUnitFamily_allCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
end
end ProximityPrize.SubmissionLower.RCN028
end PackedLegacy_DI

/-! Packed from ProximityPrize.SubmissionLower.DK. -/
section PackedLegacy_DK
namespace ProximityPrize.SubmissionLower.RCN032
open scoped Classical BigOperators
open RCN042 RCN344 RCN022
noncomputable section
set_option autoImplicit false
theorem sum_mul_eq_active_subtype
   {I:Type*} [Fintype I]
   (active:I → Prop) [DecidablePred active]
   (multiplicity cost:I → ℕ)
   (hzero:∀ i,¬ active i → cost i=0):
   (∑ i,multiplicity i*cost i)=
     ∑ i:{i//active i},multiplicity i.1*cost i.1:=by
 let f:I → ℕ:=fun i↦multiplicity i*cost i
 calc
   (∑ i,multiplicity i*cost i)=
       ∑ i∈(Finset.univ.filter active),f i:=by
     symm
     apply Finset.sum_subset (Finset.filter_subset active Finset.univ)
     intro i _ hi
     have hnot:¬ active i:=by simpa using hi
     simp [f,hzero i hnot]
   _=∑ i:{i//active i},multiplicity i.1*cost i.1:=by
     simpa only [f,Finset.subtype_univ] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset I)) f (p:=active)).symm
theorem sum_mul_coordinateOfGate_eq_active
   {K:Type} [Field K] [IsAlgClosed K]
   {I:Type*} [Fintype I]
   (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (x:∀ i,E i)
   (hgate:∀ i,∀ hx:Transcendental K (x i),
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) (E i))∧
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) (E i)))
   (multiplicity:I → ℕ):
   (∑ i,multiplicity i*coordinateDegree K (E i)
     (coordinateOfGate (K:=K) (L:=E i) (x i) (hgate i)))=
   ∑ i:{i//Transcendental K (x i)},
     multiplicity i.1*coordinateDegree K (E i.1)
       (coordinateOfGate (K:=K) (L:=E i.1) (x i.1) (hgate i.1)):=by
 classical
 apply sum_mul_eq_active_subtype
 intro i hi
 change ¬¬ IsAlgebraic K (x i) at hi
 exact coordinateOfGate_degree_of_isAlgebraic
   (K:=K) (L:=E i) (x i) (hgate i) (not_not.mp hi)
end
end ProximityPrize.SubmissionLower.RCN032
end PackedLegacy_DK

/-! Packed from ProximityPrize.SubmissionLower.DL. -/
section PackedLegacy_DL
namespace ProximityPrize.SubmissionLower.RCN033
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN343 RCN338
noncomputable section
set_option autoImplicit false
variable {Base Omega:Type} [Field Base] [Field Omega]
local instance _root_.ProximityPrize.SubmissionLower.RCN033.instDecidableEq_proximityPrize :DecidableEq Base:=Classical.decEq Base
variable {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag:FlagDegree}
theorem regularComponentWeightedInertiaCertificate_of_active_channels
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   {zIndex uIndex:Type*} [Fintype zIndex] [Fintype uIndex]
   (zComponent:zIndex → RegularComponent Omega G T H)
   (uComponent:uIndex → RegularComponent Omega G T H)
   (zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a))
   (uRewrite:(∑ C,multiplicity C*B.yzCost C)=
     ∑ a:uIndex,multiplicity (uComponent a)*B.yzCost (uComponent a))
   (zChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag firstTailFlag unitZFlag))
   (uChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (uComponent a))
     (fun a↦B.yzCost (uComponent a))
     (flagMixed surfaceFlag firstTailFlag unitYZFlag))
   (allChannel:WeightedGroupedResultantChannel (Base:=Base) multiplicity
     B.allCost (flagMixed surfaceFlag firstTailFlag unitAllFlag)):
   RegularComponentWeightedInertiaResultantCertificate B multiplicity where
 z:=by
   rw [zRewrite]
   exact zChannel.sum_mul_cost_le
 yz:=by
   rw [uRewrite]
   exact uChannel.sum_mul_cost_le
 all:=allChannel.sum_mul_cost_le
end
end ProximityPrize.SubmissionLower.RCN033
end PackedLegacy_DL

/-! Packed from ProximityPrize.SubmissionLower.DH. -/
section PackedLegacy_DH
namespace ProximityPrize.SubmissionLower.RCN027
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN042 RCN344 RCN037 RCN038 RCN095 RCN031 RCN030 RCN029 RCN028 RCN032 RCN033 RCN343 RCN342 RCN338
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedWeightedCertificate:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity:=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let B:=U.toPrimeFlagBudgetFamily
 let zIndex:=ActiveNestedZIndex (G:=G) (T:=T) (H:=H)
 let zComponent:=activeNestedZComponent (G:=G) (T:=T) (H:=H)
 let zChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:zIndex↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
   by_cases hz:Nonempty zIndex
   · letI:Nonempty zIndex:=hz
     exact activeNestedZChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty zIndex:=⟨fun a↦hz ⟨a⟩⟩
     exact emptyChannel _ _ _
 let uChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.yzCost (flagMixed surfaceFlag tailFlag unitYZFlag):=by
   by_cases hu:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hu
     exact activeNestedUChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hu ⟨C⟩⟩
     exact emptyChannel _ _ _
 let allChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.allCost (flagMixed surfaceFlag tailFlag unitAllFlag):=by
   by_cases hv:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hv
     exact activeNestedVChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hv ⟨C⟩⟩
     exact emptyChannel _ _ _
 have zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a):=by
   calc
     _=∑ C,multiplicity C*coordinateDegree Omega
         (CoordinateField Omega C.1)
         (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
     _=∑ a:zIndex,multiplicity a.1*coordinateDegree Omega
         (CoordinateField Omega a.1.1)
         (coordinateOfGate (coordinate Omega a.1.1 2) (hZ a.1)):=
       sum_mul_coordinateOfGate_eq_active
         (fun C:RegularComponent Omega G T H↦CoordinateField Omega C.1)
         (fun C↦coordinate Omega C.1 2) hZ multiplicity
     _=_:=by
       apply Finset.sum_congr rfl
       intro a _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
       rfl
 exact regularComponentWeightedInertiaCertificate_of_active_channels B
   multiplicity zComponent (fun C:RegularComponent Omega G T H↦C)
   zRewrite rfl zChannel uChannel allChannel
end
end ProximityPrize.SubmissionLower.RCN027
end PackedLegacy_DH

/-! Packed from ProximityPrize.SubmissionLower.Q1. -/
section PackedLegacy_Q1
namespace ProximityPrize.SubmissionLower.RCN334
open scoped Classical BigOperators
open RCN135 RCN136 RCN319 RCN174 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN090 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN037 RCN038 RCN042 RCN341 RCN312 RCN339 RCN330 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN334.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN334.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
 {tightSupport:ResidualSupportParameters}
def loosenStageGeneral
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport) :
   Stage K I Gamma x p flag stageErrorCap tightSupport:=S
theorem loosenStageGeneral_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStageGeneral S)
     (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStageGeneral S) hfirstProper
theorem laterTail_in_reduced_delay_secondFlag
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (C:FirstTailComponent S) (delay:ℕ) (hdelay:1 ≤ delay) :
   PolynomialInFlagMod C.1
     (delay • reducedResidualAgreementFlag tightSupport (w + 2))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
 let d:=w + 1 + delay
 let Tred:=reducedGlobalTailCut (polynomialEmbedding K) tightSupport S.F d
 let Hsupport:ResidualSupportData tightSupport S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hred:PolynomialInFlag (reducedResidualAgreementFlag tightSupport d) Tred :=
   reducedGlobalTailCut_in_flag (polynomialEmbedding K) tightSupport Hsupport d
 have hflag:PolynomialInFlag
     (delay • reducedResidualAgreementFlag tightSupport (w + 2)) Tred:=by
   have hscale:d ≤ delay * (w + 2):=by
     dsimp only [d]
     norm_num [w]
     omega
   have hallFlag:(reducedResidualAgreementFlag tightSupport d).all ≤
       (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     simp only [reducedResidualAgreementFlag, reducedAgreementDirection, nsmul_all]
     calc
       (2 * tightSupport.s - 2) * d ≤
           (2 * tightSupport.s - 2) * (delay * (w + 2)) :=
         Nat.mul_le_mul_left _ hscale
       _ = delay * ((2 * tightSupport.s - 2) * (w + 2)):=by ring
   have hysFlag :
       (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_ys]
     simp only [nsmul_yz, nsmul_all]
     rw [← Nat.mul_add]
     rw [reducedResidualAgreementFlag_ys]
     calc
       1 + d * (2 * tightSupport.ys - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.ys - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.ys - 2)):=by ring
   have htotalFlag :
       (reducedResidualAgreementFlag tightSupport d).zOnly +
           (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).zOnly +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_total]
     simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
     rw [← Nat.mul_add, ← Nat.mul_add]
     rw [reducedResidualAgreementFlag_total]
     calc
       1 + d * (2 * tightSupport.total - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.total - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.total - 2)):=by ring
   intro exponent hexponent
   have h:=hred exponent hexponent
   exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag, h.2.2.trans htotalFlag⟩
 refine ⟨Tred, hflag, ?_⟩
 have hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) tightSupport S.F d)
 exact C.1.mem_of_dvd hd
   (regularComponent_G_mem (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) C)
structure ReducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) where
 base:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   SeparableLiteralCoordinate C.1
 hactive:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0 ∨
     KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F), LiteralProjectionGate C 2
 data:AdaptiveNestedProjectionDataActive base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
 lam_poly:data.lam∈Set.range (polynomialEmbedding K)
 mu_poly:data.mu∈Set.range (polynomialEmbedding K)
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, -⟩ :=
   exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 obtain ⟨D, hlam, hmu⟩:=exists_adaptiveNestedProjectionDataActive_in base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) (Set.range (polynomialEmbedding K))
   (Set.infinite_range_of_injective (polynomialEmbedding_injective K))
 exact ⟨⟨base, hactive, hZ, D, hlam, hmu⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
theorem loosenStageGeneral_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStageGeneral S)
         (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
end
end ProximityPrize.SubmissionLower.RCN334
end PackedLegacy_Q1
end Compact_PackedLegacy


