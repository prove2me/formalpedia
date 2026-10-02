-- Prove2me | Definitions.Def_Yukon_031fc7732b9b4aeb0f27d711
-- name    : Yukon_031fc7732b9b4aeb0f27d711
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T03:47:58.860954+00:00
-- url     : https://prove2.me/theorems/aeae8cfb-ed62-4d65-9d94-bc6e50c0b753
-- title:
--   LowerFoundation source part 3/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:foundation-direct-db2eb7c1fd39b7ee35b719c76964d9809b3108bd772f5c52e1de868dc62e76d1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzJiMzIzOWY1NDhmM2RlZjZjZTdhZDQ3YmRlYmZmMzZlYzZhZWE5OWJlMTFkNjA3OWVmYzkzMzdjYTNjMTcyMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWRiMmViN2MxZmQzOWI3ZWUzNWI3MTljNzY5NjRkOTgwOWIzMTA4YmQ3NzJmNWM1MmUxZGU4NjhkYzYyZTc2ZDEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wMzFmYzc3MzJiOWI0YWViMGYyN2Q3MTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f3cc0d05eb1bfd64c84e78cc






















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.GT. -/
section PackedLegacy_GT
namespace ProximityPrize.SubmissionLower.RCN322
open RCN371 RCN011 RCN009
 RCN013
 RCN022 RCN021
 RCN024
 RCN129
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L]
set_option maxHeartbeats 1000000
theorem trdeg_le_one_of_generated_relations
   (v:Fin 3 → L)
   (hgen:IntermediateField.adjoin K (Set.range v)=⊤)
   (F T:MvPolynomial (Fin 3) K)
   (hF:Irreducible F) (hproper:¬ F∣T)
   (hFzero:MvPolynomial.aeval v F=0)
   (hTzero:MvPolynomial.aeval v T=0):Algebra.trdeg K L ≤ 1:=by
 classical
 by_cases halg:∀ i,IsAlgebraic K (v i)
 · have hA:=IntermediateField.isAlgebraic_adjoin
     (K:=K) (L:=L) (S:=Set.range v) (by
       rintro x ⟨i,rfl⟩
       exact isAlgebraic_iff_isIntegral.mp (halg i))
   rw [hgen] at hA
   letI:=hA
   letI:Algebra.IsAlgebraic K L:=(IntermediateField.topEquiv).isAlgebraic
   exact (trdeg_eq_zero (R:=K) (A:=L)).trans_le zero_le
 push Not at halg
 obtain ⟨i,hi⟩:=halg
 let e:Original K →ₐ[K] L:=MvPolynomial.aeval v
 let initial:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hi0:initial 0=i:=Equiv.swap_apply_left _ _
 have ht0:Transcendental K (e (MvPolynomial.X (initial 0))):=by
   simpa [e,hi0] using (show Transcendental K (v i) from hi)
 have hex:∃ order:Fin 3 ≃ Fin 3,
     Transcendental K (e (MvPolynomial.X (order 0)))∧
     0 < (planeMap K order F).natDegree:=by
   have hirr:=rationalMap_irreducible_of_evaluation K L initial e F hF hFzero ht0
   rcases positive_degree_of_irreducible (rationalMap K initial F) hirr with h0 | h1
   · refine ⟨initial,ht0,?_⟩
     change 0 < (bivariateEquiv (RatFunc K) (rationalMap K initial F)).natDegree
     rwa [bivariateEquiv_natDegree]
   · exact ⟨swapOtherOrder initial,by simpa only [swapOtherOrder_zero] using ht0,
       by rwa [swapped_outer_degree]⟩
 obtain ⟨order,ht,hpositive⟩:=hex
 let base:=elementEmbedding K L (e (MvPolynomial.X (order 0))) ht
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hpair:IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤:=by
   let S:=IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)
   have hcoords:Set.range v ⊆ S.restrictScalars K:=by
     rintro x ⟨l,rfl⟩
     obtain ⟨j,rfl⟩:=order.surjective l
     have hj:j=0∨j=1∨j=2:=by omega
     rcases hj with rfl | rfl | rfl
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
       change elementEmbedding K L _ ht _∈S at hm
       rw [elementEmbedding_variable] at hm
       simpa [e] using hm
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_right (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_left (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   have htop:S.restrictScalars K=⊤:=by
     apply top_unique
     rw [←hgen]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
 have hroot (G:Original K) (hG:e G=0):
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (RatFunc K) L)
       (e (MvPolynomial.X (order 2))))
       (e (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
   rw [←RCN365.planeEval_eq_eval₂]
   change planeEvaluation K L order e ht (planeMap K order G)=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   exact hG
 have hirr:=planeMap_irreducible_of_evaluation K L order e F hF hFzero ht
 have hproperPlane:¬ planeMap K order F∣planeMap K order T:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_evaluation K L order e F T hF hFzero ht).mp h)
 letI:FiniteDimensional (RatFunc K) L:=finite_of_proper_plane_roots
   (planeMap K order F) (planeMap K order T) hirr hpositive hproperPlane
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   (hroot F hFzero) (hroot T hTzero) hpair
 exact trdeg_le_one_of_functionField K L
end
end ProximityPrize.SubmissionLower.RCN322
end PackedLegacy_GT

/-! Packed from ProximityPrize.SubmissionLower.EG. -/
section PackedLegacy_EG
namespace ProximityPrize.SubmissionLower.RCN127
open RCN077 RCN319 RCN136
 RCN132 RCN126
 RCN062
 RCN322 RCN129
 RCN022
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
public def freshJet (P:Polynomial L) (γ:L) (i:Fin 4):
   jetField (k:=k) P γ:=
 ⟨freshPoint P γ i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
@[simp] private theorem freshJet_val (P:Polynomial L) (γ:L) (i:Fin 4):
   ((freshJet (k:=k) P γ i:jetField (k:=k) P γ):RatFunc L)=
     freshPoint P γ i:=rfl
public def freshOtherJet (P:Polynomial L) (γ:L) (i:Fin 3):
   jetField (k:=k) P γ:=freshJet (k:=k) P γ i.succ
public theorem freshTau_transcendental (P:Polynomial L) (γ:L):
   Transcendental k (freshJet (k:=k) P γ 0):=by
 intro h
 have h':IsAlgebraic k (RatFunc.X:RatFunc L):=by
   exact IntermediateField.isAlgebraic_iff.mp h
 exact (RatFunc.transcendental_X.restrictScalars
   (algebraMap k L).injective) h'
set_option maxHeartbeats 1000000 in
theorem baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
   (F T:Poly4 k) (P:Polynomial L) (γ:L)
   (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (hproper:¬ F∣T)
   (hFsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) F)=0)
   (hTsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) T)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4)
       (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 classical
 let E:=jetField (k:=k) P γ
 let full:Fin 4 → E:=freshJet (k:=k) P γ
 let v:Fin 3 → E:=freshOtherJet (k:=k) P γ
 let τ:E:=freshJet (k:=k) P γ 0
 have hτ:Transcendental k τ:=freshTau_transcendental P γ
 let rawEquiv:=FractionRing.algEquiv (Polynomial k) (RatFunc k)
 let coeffEquiv:RationalCoefficients k ≃ₐ[k] RatFunc k:=rawEquiv.restrictScalars k
 let baseRat:RatFunc k →ₐ[k] E:=elementEmbedding k E τ hτ
 let base:RationalCoefficients k →ₐ[k] E:=baseRat.comp coeffEquiv.toAlgHom
 letI:Algebra (RationalCoefficients k) E:=base.toRingHom.toAlgebra
 letI:IsScalarTower k (RationalCoefficients k) E:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hbaseX:base
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=τ:=by
   change baseRat (rawEquiv
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X))=τ
   rw [rawEquiv.commutes,elementEmbedding_variable]
 have hfull:IntermediateField.adjoin k (Set.range full)=⊤:=by
   apply IntermediateField.map_injective E.val
   rw [IntermediateField.adjoin_map, ←AlgHom.fieldRange_eq_map,
     IntermediateField.fieldRange_val]
   have himage:E.val '' Set.range full=Set.range (freshPoint P γ):=by
     ext x
     simp [full,freshJet]
   rw [himage]
   rfl
 have hgen:IntermediateField.adjoin (RationalCoefficients k) (Set.range v)=⊤:=by
   let S:=IntermediateField.adjoin (RationalCoefficients k) (Set.range v)
   have hcoords:Set.range full ⊆ S.restrictScalars k:=by
     rintro x ⟨i,rfl⟩
     refine Fin.cases ?_ (fun j↦?_) i
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)∈S at hm
       rw [hbaseX] at hm
       exact hm
     · exact IntermediateField.subset_adjoin (RationalCoefficients k) _ ⟨j,rfl⟩
   have htop:S.restrictScalars k=⊤:=by
     apply top_unique
     rw [←hfull]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp htop
 have hsurface:∀ G:Poly4 k,
     MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
         (rationalSurfaceMap k G)=
       MvPolynomial.eval₂Hom (algebraMap k E) full G:=by
   intro G
   have heq:(MvPolynomial.eval₂Hom
         (algebraMap (RationalCoefficients k) E) v).comp (rationalSurfaceMap k)=
       MvPolynomial.eval₂Hom (algebraMap k E) full:=by
     apply MvPolynomial.ringHom_ext
     · intro a
       simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_C,
         MvPolynomial.eval₂Hom_C]
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) (Polynomial.C a))=
           algebraMap k E a
       calc
         _=base (algebraMap k (RationalCoefficients k) a):=by
           congr 1
         _=algebraMap k E a:=base.commutes a
     · intro i
       refine Fin.cases ?_ (fun j↦?_) i
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_zero,
           MvPolynomial.eval₂Hom_C,
           MvPolynomial.eval₂Hom_X']
         change base
           (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=full 0
         exact hbaseX
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_succ,
           MvPolynomial.eval₂Hom_X']
         rfl
   exact RingHom.congr_fun heq G
 have hcoeffcomp:E.val.toRingHom.comp
       (MvPolynomial.eval₂Hom (algebraMap k E) full)=
     (MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)).comp
       (MvPolynomial.map (algebraMap k L)):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_C,
       MvPolynomial.map_C]
     change algebraMap k (RatFunc L) a=
       algebraMap L (RatFunc L) (algebraMap k L a)
     exact IsScalarTower.algebraMap_apply k L (RatFunc L) a
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_X',
       MvPolynomial.map_X]
     change E.val (full i)=freshPoint P γ i
     rfl
 have hfullroot (G:Poly4 k)
     (hG:specialization L P γ (MvPolynomial.map (algebraMap k L) G)=0):
     MvPolynomial.eval₂Hom (algebraMap k E) full G=0:=by
   apply E.val.injective
   change (E.val.toRingHom.comp
     (MvPolynomial.eval₂Hom (algebraMap k E) full)) G=E.val 0
   rw [hcoeffcomp,RingHom.comp_apply,fresh_eval_eq,hG,map_zero,map_zero]
 have hFroot:MvPolynomial.aeval v (rationalSurfaceMap k F)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k F)=0
   rw [hsurface]
   exact hfullroot F hFsolution
 have hTroot:MvPolynomial.aeval v (rationalSurfaceMap k T)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k T)=0
   rw [hsurface]
   exact hfullroot T hTsolution
 have hirr:Irreducible (rationalSurfaceMap k F):=
   rationalSurfaceMap_irreducible k F hF hpos
 have hproperRat:¬ rationalSurfaceMap k F∣rationalSurfaceMap k T:=by
   intro h
   exact hproper ((rationalSurfaceMap_dvd_iff k F T hF hpos).mp h)
 have hrelative:Algebra.trdeg (RationalCoefficients k) E ≤ 1:=
   trdeg_le_one_of_generated_relations (RationalCoefficients k) E v hgen
     (rationalSurfaceMap k F) (rationalSurfaceMap k T)
     hirr hproperRat hFroot hTroot
 have hbaseRat:Algebra.trdeg k (RatFunc k) ≤ 1:=
   trdeg_le_one_of_functionField k (RatFunc k)
 have hbase:Algebra.trdeg k (RationalCoefficients k) ≤ 1:=by
   rw [coeffEquiv.trdeg_eq]
   exact hbaseRat
 have hsum:Algebra.trdeg k (RationalCoefficients k)+
     Algebra.trdeg (RationalCoefficients k) E=Algebra.trdeg k E:=
   trdeg_add_eq k (RationalCoefficients k)
 have hjet:Algebra.trdeg k E ≤ 2:=by
   rw [←hsum]
   exact (add_le_add hbase hrelative).trans_eq (by norm_num)
 have hfield:=fresh_jetField_eq_coefficientField F P γ hFsolution hreg p w hw hP
 change Algebra.trdeg k (jetField (k:=k) P γ) ≤ 2 at hjet
 rw [hfield] at hjet
 exact baseCoefficientField_trdeg_le_one P γ hjet
end
end ProximityPrize.SubmissionLower.RCN127
end PackedLegacy_EG

/-! Packed from ProximityPrize.SubmissionLower.H9. -/
section PackedLegacy_H9
namespace ProximityPrize.SubmissionLower.RCN059
open scoped BigOperators
noncomputable section
variable {k F L Γ:Type*} [Field k] [Field F] [Field L]
 [LinearOrderedCommGroupWithZero Γ]
local instance _root_.ProximityPrize.SubmissionLower.RCN059.instDecidableEq_proximityPrize :DecidableEq F:=Classical.decEq F
def ResidueApprox (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F):Prop:=
 ∀ f:F,v (φ f) ≤ 1 → ∃ c:k,v (φ (f-κ c)) < 1
def ConstantPolynomialUnit (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (w:ℕ):Prop:=
 ∀ c:Fin (w+1) → k,(∃ i,c i≠0) →
   v (∑ i,φ (κ (c i))*x^(i:ℕ))=1
public theorem sum_eq_one_of_close {w:ℕ}
   (v:Valuation L Γ) (x:L) (hx:v x=1)
   (b c:Fin (w+1) → L)
   (hclose:∀ i,v (b i-c i) < 1)
   (hc:v (∑ i,c i*x^(i:ℕ))=1):
   v (∑ i,b i*x^(i:ℕ))=1:=by
 have herr:v (∑ i,(b i-c i)*x^(i:ℕ)) < 1:=by
   apply v.map_sum_lt (by simp)
   intro i _
   simpa only [map_mul,map_pow,hx,one_pow,mul_one] using hclose i
 have hsplit:(∑ i,b i*x^(i:ℕ))=
     (∑ i,c i*x^(i:ℕ))+
     (∑ i,(b i-c i)*x^(i:ℕ)):=by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro i _
   ring
 rw [hsplit,v.map_add_eq_of_lt_left (by simpa only [hc] using herr),hc]
theorem valuation_sum_eq_dominant_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (j:Fin (w+1)) (haj:a j≠0)
   (hmax:∀ i,v (φ (a i)) ≤ v (φ (a j))):
   v (∑ i,φ (a i)*x^(i:ℕ))=v (φ (a j)):=by
 have hφj:φ (a j)≠0:=by
   intro h
   apply haj
   apply φ.injective
   simpa using h
 have hvj:v (φ (a j))≠0:=(Valuation.ne_zero_iff v).mpr hφj
 have hnorm:∀ i,v (φ (a i/a j)) ≤ 1:=by
   intro i
   rw [map_div₀,map_div₀]
   exact (div_le_one₀ (zero_lt_iff.mpr hvj)).mpr (hmax i)
 choose c hc using fun i => hres (a i/a j) (hnorm i)
 have hcj:c j≠0:=by
   intro h
   have hbad:=hc j
   simpa [h,haj] using hbad
 have hsum:v (∑ i,φ (a i/a j)*x^(i:ℕ))=1:=by
   apply sum_eq_one_of_close v x hx
     (fun i => φ (a i/a j)) (fun i => φ (κ (c i)))
   · intro i
     simpa only [map_sub] using hc i
   · exact hunit c ⟨j,hcj⟩
 have hscale:(∑ i,φ (a i)*x^(i:ℕ))=
     φ (a j)*(∑ i,φ (a i/a j)*x^(i:ℕ)):=by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [map_div₀]
   field_simp
 rw [hscale,map_mul,hsum,mul_one]
theorem valuation_coefficient_le_sum_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   v (φ (a i)) ≤ v (∑ j,φ (a j)*x^(j:ℕ)):=by
 classical
 by_cases hai:a i=0
 · simp [hai]
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 obtain ⟨j,_,hmax⟩:=
   Finset.exists_max_image Finset.univ (fun j:Fin (w+1) => v (φ (a j)))
     Finset.univ_nonempty
 have haj:a j≠0:=by
   intro h
   have hz:v (φ (a j))=0:=by simp [h]
   apply hvi
   apply le_antisymm
   · simpa only [hz] using hmax i (Finset.mem_univ i)
   · exact zero_le
 rw [valuation_sum_eq_dominant_of_residueApprox v φ κ x hx hres hunit a j haj
   (fun z => hmax z (Finset.mem_univ z))]
 exact hmax i (Finset.mem_univ i)
theorem coefficient_pole_le_generic_value_of_residueApprox {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 have hval:=valuation_coefficient_le_sum_of_residueApprox
   v φ κ x hx hres hunit a i
 by_cases hai:a i=0
 · simp only [hai,map_zero,RCN187.poleOrder,
     WithZero.log_zero,max_self]
   exact le_max_left _ _
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 have hsum:v (∑ j,φ (a j)*x^(j:ℕ))≠0:=
   ne_of_gt ((zero_lt_iff.mpr hvi).trans_le hval)
 exact max_le_max_left 0 ((WithZero.log_le_log hvi hsum).mpr hval)
end
end ProximityPrize.SubmissionLower.RCN059
end PackedLegacy_H9

/-! Packed from ProximityPrize.SubmissionLower.I0. -/
section PackedLegacy_I0
namespace ProximityPrize.SubmissionLower.RCN060
open scoped BigOperators
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k F Γ:Type*} [Field k] [Field F] [Algebra k F]
 [LinearOrderedCommGroupWithZero Γ]
local instance _root_.ProximityPrize.SubmissionLower.RCN060.instDecidableEq_proximityPrize :DecidableEq k:=Classical.decEq k
local instance _root_.ProximityPrize.SubmissionLower.RCN060.instDecidableEq_proximityPrize_1 :DecidableEq F:=Classical.decEq F
theorem polynomial_value_le_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1) (f:F) (hf:v f ≤ 1) (p:k[X]):
   v (p.eval₂ κ f) ≤ 1:=by
 rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro i _
 rw [map_mul,map_pow]
 exact mul_le_one₀ (hκ _) zero_le (pow_le_one₀ zero_le hf)
theorem normalize_relation
   {R:Type*} [CommRing R] [IsDomain R] (κ:R →+*F)
   (u:F) (hu:u≠0) (p:R[X]) (hp:p≠0)
   (hev:p.eval₂ κ u=0):
   ∃ q:R[X],q.coeff 0≠0∧q.eval₂ κ u=0:=by
 classical
 induction hn:p.natDegree using Nat.strong_induction_on generalizing p with
 | h n ih =>
   by_cases hzero:p.coeff 0=0
   · obtain ⟨q,hpq⟩:=Polynomial.X_dvd_iff.mpr hzero
     have hq:q≠0:=by
       intro hz
       exact hp (by simp [hpq,hz])
     have hdeg:q.natDegree < n:=by
       rw [hpq,Polynomial.natDegree_X_mul hq] at hn
       omega
     have hqeval:q.eval₂ κ u=0:=by
       rw [hpq,Polynomial.eval₂_mul,Polynomial.eval₂_X] at hev
       exact (mul_eq_zero.mp hev).resolve_left hu
     exact ih q.natDegree hdeg q hq hqeval rfl
   · exact ⟨p,hzero,hev⟩
theorem exists_constant_close_of_small_polynomial [IsAlgClosed k]
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,c≠0 → v (κ c)=1)
   (f:F) (p:k[X]) (hp:p≠0) (hsmall:v (p.eval₂ κ f) < 1):
   ∃ c:k,v (f-κ c) < 1:=by
 classical
 by_contra h
 push_neg at h
 have hge:1 ≤ v (p.eval₂ κ f):=by
   rw [(IsAlgClosed.splits p).eq_prod_roots,Polynomial.eval₂_mul,
     Polynomial.eval₂_C,map_mul,hκ p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp),
     one_mul,Polynomial.eval₂_multiset_prod,map_multiset_prod]
   simp only [Multiset.map_map,Polynomial.eval₂_sub,Polynomial.eval₂_X,
     Polynomial.eval₂_C,Function.comp_def]
   exact Multiset.one_le_prod_map (fun c _ => h c)
 exact (not_lt_of_ge hge) hsmall
theorem constant_coefficient_value_lt_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1)
   (u f:F) (hu:v u < 1) (hf:v f ≤ 1)
   (q:Polynomial (Polynomial k))
   (hq:q.eval₂ (Polynomial.eval₂RingHom κ f) u=0):
   v ((q.coeff 0).eval₂ κ f) < 1:=by
 have hcoeff:∀ p:k[X],v ((Polynomial.eval₂RingHom κ f) p) ≤ 1:=
   fun p => polynomial_value_le_one v κ hκ f hf p
 have htail:v (q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u) ≤ 1:=by
   rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
   apply v.map_sum_le
   intro i _
   rw [map_mul,map_pow]
   exact mul_le_one₀ (hcoeff _) zero_le (pow_le_one₀ zero_le hu.le)
 have hdecomp:=congrArg
   (fun p:Polynomial (Polynomial k) => p.eval₂ (Polynomial.eval₂RingHom κ f) u)
   (Polynomial.X_mul_divX_add q)
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_X,
   Polynomial.eval₂_C,hq,Polynomial.coe_eval₂RingHom] at hdecomp
 have heq:(q.coeff 0).eval₂ κ f=
     -(u*q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u):=by
   rw [eq_neg_iff_add_eq_zero]
   simpa only [add_comm] using hdecomp
 rw [heq,v.map_neg,map_mul]
 exact (mul_le_mul' le_rfl htail).trans_lt (by simpa using hu)
theorem exists_bivariate_relation_of_trdeg_one
   (htrdeg:Algebra.trdeg k F=1) (u f:F):
   ∃ q:Polynomial (Polynomial k),q≠0∧
     q.eval₂ (Polynomial.eval₂RingHom (algebraMap k F) f) u=0:=by
 have hnot:¬ AlgebraicIndependent k ![f,u]:=by
   intro hi
   have hc:=hi.lift_cardinalMk_le_trdeg
   rw [htrdeg] at hc
   norm_num at hc
 rw [algebraicIndependent_iff] at hnot
 push_neg at hnot
 obtain ⟨p,hpval,hp⟩:=hnot
 let e:=Polynomial.Bivariate.equivMvPolynomial k
 let q:Polynomial (Polynomial k):=e.symm p
 have hq:q≠0:=by
   intro hz
   apply hp
   have:=congrArg e hz
   simpa [q] using this
 have hmaps:
     (Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom=
       MvPolynomial.aeval ![f,u]:=by
   ext i
   fin_cases i <;> simp [e,Polynomial.aevalAeval_C,
     Polynomial.aevalAeval_X,Polynomial.aevalAeval_Y]
 have hev:
     Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u=
       (Polynomial.aevalAeval (R:=k) f u).toRingHom:=by
   ext <;> simp [Polynomial.aevalAeval_C,Polynomial.aevalAeval_X,
     Polynomial.aevalAeval_Y]
 refine ⟨q,hq,?_⟩
 change (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u) q=0
 rw [hev]
 change ((Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom) p=0
 rw [hmaps]
 exact hpval
theorem exists_constant_approx_of_trdeg_one [IsAlgClosed k]
   (v:Valuation F Γ) [v.IsTrivialOn k]
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v u < 1)
   (f:F) (hf:v f ≤ 1):
   ∃ c:k,v (f-algebraMap k F c) < 1:=by
 have hκ:∀ c:k,v (algebraMap k F c) ≤ 1:=by
   intro c
   by_cases hc:c=0
   · simp [hc]
   · exact (Valuation.IsTrivialOn.eq_one c hc).le
 obtain ⟨p,hp,hpval⟩:=exists_bivariate_relation_of_trdeg_one htrdeg u f
 obtain ⟨q,hq0,hqval⟩:=
   normalize_relation (Polynomial.eval₂RingHom (algebraMap k F) f) u hu0 p hp hpval
 exact exists_constant_close_of_small_polynomial v (algebraMap k F)
   (fun c hc => Valuation.IsTrivialOn.eq_one c hc) f (q.coeff 0) hq0
   (constant_coefficient_value_lt_one v (algebraMap k F) hκ u f hu hf q hqval)
variable {L:Type*} [Field L]
open ProximityPrize.SubmissionLower RCN059
theorem residueApprox_of_trdeg_one [IsAlgClosed k]
   (v:Valuation L Γ) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v (φ u) < 1):
   ResidueApprox v φ (algebraMap k F):=by
 let vF:Valuation F Γ:=v.comap φ
 letI:vF.IsTrivialOn k:=⟨hconst⟩
 intro f hf
 exact exists_constant_approx_of_trdeg_one vF htrdeg u hu0 hu f hf
theorem coefficient_pole_le_of_trdeg_one [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (x:L) (hx:v x=1)
   (hunit:ConstantPolynomialUnit v φ (algebraMap k F) x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 by_cases hi:v (φ (a i)) ≤ 1
 · have hz:RCN187.poleOrder v (φ (a i))=0:=by
     change max 0 (v (φ (a i))).log=0
     rw [←RCN187.log_max_one,max_eq_left hi,WithZero.log_one]
   rw [hz]
   exact le_max_left _ _
 have hbig:1 < v (φ (a i)):=lt_of_not_ge hi
 let vF:Valuation F (WithZero (Multiplicative ℤ)):=v.comap φ
 haveI:vF.IsNontrivial:=
   ⟨a i,ne_of_gt (zero_lt_one.trans hbig),hbig.ne'⟩
 obtain ⟨u,hu0,hu⟩:=Valuation.IsNontrivial.exists_lt_one (v:=vF)
 exact coefficient_pole_le_generic_value_of_residueApprox v φ (algebraMap k F)
   x hx (residueApprox_of_trdeg_one v φ hconst htrdeg u hu0 hu) hunit a i
theorem constantPolynomialUnit_of_base_constants
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] {w:ℕ}
   (v:Valuation L Γ) [v.IsTrivialOn Ω] (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (x:Ω) (htrans:Transcendental k x):
   ConstantPolynomialUnit v φ (algebraMap k F) (algebraMap Ω L x) w:=by
 classical
 intro c hc
 obtain ⟨i,hi⟩:=hc
 let q:k[X]:=∑ j:Fin (w+1),Polynomial.monomial (j:ℕ) (c j)
 have hcoef:q.coeff (i:ℕ)=c i:=by
   simp only [q,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
   rw [Finset.sum_eq_single i]
   · simp
   · intro j _ hji
     have hval:(j:ℕ)≠(i:ℕ):=fun h => hji (Fin.ext h)
     simp [hval]
   · simp
 have hq:q≠0:=by
   intro hzero
   apply hi
   have h:=congrArg (fun p:k[X] => p.coeff (i:ℕ)) hzero
   simpa only [hcoef,Polynomial.coeff_zero] using h
 have hneq:Polynomial.aeval x q≠0:=by
   intro hzero
   apply hq
   apply (transcendental_iff_injective.mp htrans)
   simpa only [map_zero] using hzero
 have hv:v (algebraMap Ω L (Polynomial.aeval x q))=1:=
   Valuation.IsTrivialOn.eq_one _ hneq
 simpa only [q,map_sum,Polynomial.aeval_monomial,map_mul,map_pow,
   ←hcompat] using hv
theorem coefficient_pole_le_generic_evaluation
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F=1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 have hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1:=by
   intro c hc
   rw [hcompat]
   apply Valuation.IsTrivialOn.eq_one
   intro hz
   apply hc
   apply (algebraMap k Ω).injective
   simpa using hz
 have hx0:x≠0:=by
   intro hz
   apply htrans
   rw [hz]
   exact isAlgebraic_zero
 have hx:v (algebraMap Ω L x)=1:=Valuation.IsTrivialOn.eq_one x hx0
 exact coefficient_pole_le_of_trdeg_one v φ hconst htrdeg (algebraMap Ω L x) hx
   (constantPolynomialUnit_of_base_constants v φ hcompat x htrans) a i
end
end ProximityPrize.SubmissionLower.RCN060
end PackedLegacy_I0

/-! Packed from ProximityPrize.SubmissionLower.I1. -/
section PackedLegacy_I1
namespace ProximityPrize.SubmissionLower.RCN061
open scoped BigOperators
open RCN060
noncomputable section
variable {k F L:Type*} [Field k] [Field F] [Field L] [Algebra k F]
theorem coefficient_pole_le_generic_evaluation_of_trdeg_le_one
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F ≤ 1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 classical
 letI:Decidable (Algebra.trdeg k F=0):=Classical.propDecidable _
 by_cases hz:Algebra.trdeg k F=0
 · letI:Algebra.IsAlgebraic k F:=trdeg_eq_zero_iff.mp hz
   letI:Algebra.IsIntegral k F:=
     Algebra.isAlgebraic_iff_isIntegral.mp (inferInstance:Algebra.IsAlgebraic k F)
   obtain ⟨c,hc⟩:=
     (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=k)).2 (a i)
   have hφ:φ (a i)=algebraMap Ω L (algebraMap k Ω c):=by
     rw [←hc,hcompat]
   have hpole:RCN187.poleOrder v (φ (a i))=0:=by
     rw [hφ]
     change max 0 (v (algebraMap Ω L (algebraMap k Ω c))).log=0
     rw [←RCN187.log_max_one,
       max_eq_left (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _),
       WithZero.log_one]
   rw [hpole]
   exact le_max_left _ _
 · have hone:(1:Cardinal) ≤ Algebra.trdeg k F:=
     Cardinal.one_le_iff_ne_zero.mpr hz
   have heq:Algebra.trdeg k F=1:=le_antisymm htrdeg hone
   exact coefficient_pole_le_generic_evaluation v φ hcompat heq x htrans a i
end
end ProximityPrize.SubmissionLower.RCN061
end PackedLegacy_I1

/-! Packed from ProximityPrize.SubmissionLower.D0. -/
section PackedLegacy_D0
namespace ProximityPrize.SubmissionLower.RCN205
open scoped Classical WithZero
open RCN187 RCN295 RCN095 RCN114 RCN162
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K L:Type} [Field K] [Field L] [Algebra K L]
abbrev DV (L:Type) [Field L]:=Valuation L (WithZero (Multiplicative ℤ))
public theorem pole_nonneg (ν:DV L) (x:L):0 ≤ poleOrder ν x:=
 le_max_left _ _
public theorem val_le_exp_pole (ν:DV L) (x:L):
   ν x ≤ WithZero.exp (poleOrder ν x):=by
 have hn:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 rw [poleOrder, ←log_max_one,WithZero.exp_log hn]
 exact le_max_right _ _
public theorem pole_le_of_val_le (ν:DV L) (x:L) (n:ℤ)
   (hn:0 ≤ n) (h:ν x ≤ WithZero.exp n):poleOrder ν x ≤ n:=by
 have h1:(1:WithZero (Multiplicative ℤ)) ≤ WithZero.exp n:=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact hn
 have hnz:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 have hh:=(WithZero.log_le_log hnz WithZero.exp_ne_zero).2 (max_le h1 h)
 simpa only [log_max_one,WithZero.log_exp,poleOrder] using hh
theorem pole_add_le (ν:DV L) (x y:L):
   poleOrder ν (x+y) ≤ max (poleOrder ν x) (poleOrder ν y):=by
 apply pole_le_of_val_le ν _ _ ((pole_nonneg ν x).trans (le_max_left _ _))
 exact (ν.map_add x y).trans (max_le
   ((val_le_exp_pole ν x).trans ((WithZero.exp_le_exp).2 (le_max_left _ _)))
   ((val_le_exp_pole ν y).trans ((WithZero.exp_le_exp).2 (le_max_right _ _))))
theorem pole_const_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K):
   poleOrder ν (algebraMap K L c) ≤ 0:=by
 apply pole_le_of_val_le ν _ _ le_rfl
 simpa using hν c
theorem pole_const_mul_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K) (x:L):
   poleOrder ν (algebraMap K L c*x) ≤ poleOrder ν x:=by
 apply pole_le_of_val_le ν _ _ (pole_nonneg ν x)
 rw [map_mul]
 exact (mul_le_mul' (hν c) (val_le_exp_pole ν x)).trans_eq (one_mul _)
theorem pole_neg (ν:DV L) (x:L):poleOrder ν (-x)=poleOrder ν x:=by
 simp [poleOrder]
end
end ProximityPrize.SubmissionLower.RCN205
end PackedLegacy_D0

/-! Packed from ProximityPrize.SubmissionLower.H8. -/
section PackedLegacy_H8
namespace ProximityPrize.SubmissionLower.RCN058
open RCN062 RCN061 RCN187 RCN205 RCN002
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
variable {K k L:Type} [Field K] [Field k] [Field L]
 [Algebra K k] [Algebra K L] [Algebra k L] [IsScalarTower K k L]
theorem baseCoefficientField_trdeg_le_one_of_algebraic_constants
   [Algebra.IsAlgebraic K k] (P:Polynomial L) (γ:L)
   (htr:Algebra.trdeg K (baseCoefficientField (k:=K) P γ) ≤ 1):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 let S:Set L:=insert γ (Set.range (fun j:ℕ => P.coeff j))
 let BK:IntermediateField K L:=baseCoefficientField (k:=K) P γ
 let Bk:IntermediateField k L:=baseCoefficientField (k:=k) P γ
 let BkK:IntermediateField K L:=Bk.restrictScalars K
 have hBK:BK ≤ BkK:=by
   change IntermediateField.adjoin K S ≤ BkK
   apply IntermediateField.adjoin_le_iff.mpr
   intro z hz
   change z∈Bk
   exact IntermediateField.subset_adjoin k S hz
 let inc:BK →ₐ[K] Bk:={
   toFun:=fun z => ⟨z,hBK z.2⟩
   map_one':=rfl
   map_mul':=fun _ _ => rfl
   map_zero':=rfl
   map_add':=fun _ _ => rfl
   commutes':=fun _ => rfl}
 letI:Algebra BK Bk:=inc.toRingHom.toAlgebra
 letI:IsScalarTower K BK Bk:=
   IsScalarTower.of_algebraMap_eq fun c => (inc.commutes c).symm
 letI:IsScalarTower BK Bk L:=
   IsScalarTower.of_algebraMap_eq fun _ => rfl
 let ACL:IntermediateField BK L:=algebraicClosure BK L
 have hkACL (c:k):algebraMap k L c∈ACL:=by
   apply mem_algebraicClosure_iff.mpr
   have hcK:IsAlgebraic K (algebraMap k L c):=
     (Algebra.IsAlgebraic.isAlgebraic c).algebraMap
   exact hcK.tower_top BK
 let ACLk:IntermediateField k L:=
   ACL.toSubfield.toIntermediateField hkACL
 have hBkACL:Bk ≤ ACLk:=by
   apply IntermediateField.adjoin_le_iff.mpr
   intro z hz
   change z∈ACL
   have hzBK:z∈BK:=IntermediateField.subset_adjoin K S hz
   simpa only [IntermediateField.algebraMap_apply] using
     ACL.algebraMap_mem (⟨z,hzBK⟩:BK)
 letI:Algebra.IsAlgebraic BK Bk:=⟨fun z => by
   apply (isAlgebraic_algHom_iff
     (IsScalarTower.toAlgHom BK Bk L) (algebraMap Bk L).injective).mp
   apply mem_algebraicClosure_iff.mp
   exact hBkACL z.2⟩
 have hzeroE:Algebra.trdeg BK Bk=0:=trdeg_eq_zero
 have hsumE:Algebra.trdeg K BK+Algebra.trdeg BK Bk=Algebra.trdeg K Bk:=
   trdeg_add_eq K BK
 have hKBk:Algebra.trdeg K Bk ≤ 1:=by
   rw [←hsumE,hzeroE,add_zero]
   exact htr
 have hzerok:Algebra.trdeg K k=0:=trdeg_eq_zero
 have hsumk:Algebra.trdeg K k+Algebra.trdeg k Bk=Algebra.trdeg K Bk:=
   trdeg_add_eq K k
 rw [hzerok,zero_add] at hsumk
 exact hsumk.symm ▸ hKBk
theorem coefficient_pole_le_of_trdeg_le_one
   {Ω:Type} [Field Ω] [IsAlgClosed k]
   [Algebra k Ω] [Algebra Ω L] [IsScalarTower k Ω L]
   (P:Polynomial L) (γ:L) (w:ℕ) (hP:P.natDegree ≤ w)
   (htr:Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1)
   (x:Ω) (hx:Transcendental k x) (y:L)
   (hy:P.eval (algebraMap Ω L x)=y)
   (v:RCN346.Place Ω L) (j:ℕ):
   poleOrder v.val (P.coeff j) ≤ poleOrder v.val y:=by
 letI:v.val.IsTrivialOn Ω:=v.property.2
 let B:IntermediateField k L:=baseCoefficientField (k:=k) P γ
 have hcoeff (n:ℕ):P.coeff n∈B:=by
   exact IntermediateField.subset_adjoin k _ (Or.inr ⟨n,rfl⟩)
 by_cases hj:j < w+1
 · let i:Fin (w+1):=⟨j,hj⟩
   let a:Fin (w+1) → B:=fun n => ⟨P.coeff n,hcoeff n⟩
   let φ:B →+*L:=B.val.toRingHom
   have hcompat:∀ c:k,φ (algebraMap k B c)=
       algebraMap Ω L (algebraMap k Ω c):=by
     intro c
     exact IsScalarTower.algebraMap_apply k Ω L c
   have hsum:(∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ))=
       P.eval (algebraMap Ω L x):=by
     rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
     rw [←Fin.sum_univ_eq_sum_range]
     change (∑ n:Fin (w+1),P.coeff (n:ℕ)*
       (algebraMap Ω L x)^(n:ℕ))=_
     rfl
   have hle:=coefficient_pole_le_generic_evaluation_of_trdeg_le_one
     v.val φ hcompat htr x hx a i
   change poleOrder v.val (P.coeff i) ≤
     poleOrder v.val (∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ)) at hle
   rw [hsum,hy] at hle
   simpa only [i] using hle
 · have hz:P.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt
     (hP.trans_lt (by omega))
   rw [hz]
   simp only [poleOrder,map_zero,WithZero.log_zero,max_self]
   exact le_max_left _ _
end
end ProximityPrize.SubmissionLower.RCN058
end PackedLegacy_H8

/-! Packed from ProximityPrize.SubmissionLower.A8. -/
section PackedLegacy_A8
namespace ProximityPrize.SubmissionLower.RCN063
open scoped Classical BigOperators WithZero
open RCN187 RCN205 RCN344 RCN002 RCN065 RCN136 RCN139 RCN047 RCN313 RCN233 RCN238 RCN341 RCN271 RCN257 RCN095 RCN114 RCN295
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {L:Type} [Field L]
def coefficientPoleWeight (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):ℤ:=
 (insert (0:ℤ) (insert (poleOrder v z)
   (T.support.image (fun j↦poleOrder v (T.coeff j))))).max'
   ⟨0,Finset.mem_insert_self _ _⟩
theorem coefficientPoleWeight_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):0 ≤ coefficientPoleWeight v T z:=
 Finset.le_max' _ _ (Finset.mem_insert_self _ _)
theorem seedPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):poleOrder v z ≤ coefficientPoleWeight v T z:=
 Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
theorem coeffPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L) (j:ℕ) (hj:j∈T.support):
   poleOrder v (T.coeff j) ≤ coefficientPoleWeight v T z:=by
 unfold coefficientPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
public theorem pole_le_of_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:L) (q:ℤ) (hq:0 ≤ q) (hx:v x ≤ WithZero.exp q):poleOrder v x ≤ q:=by
 apply max_le hq
 by_cases hzero:v x=0
 · simpa [hzero] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hzero WithZero.exp_ne_zero).mpr hx
theorem eval_pole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z a:L) (ha:v a ≤ 1):
   poleOrder v (T.eval a) ≤ coefficientPoleWeight v T z:=by
 apply pole_le_of_exp _ _ _ (coefficientPoleWeight_nonneg v T z)
 rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro j hj
 rw [map_mul,map_pow]
 have hc:v (T.coeff j) ≤ WithZero.exp (coefficientPoleWeight v T z):=
   WithZero.le_exp_of_log_le ((le_max_right _ _).trans (coeffPole_le v T z j hj))
 have hp:v a^j ≤ 1:=pow_le_one₀ zero_le ha
 simpa only [mul_one] using mul_le_mul' hc hp
theorem affine_eval_pole_le {Ω:Type} [Field Ω] [Algebra Ω L]
   (v:Place Ω L) (T:Polynomial L) (z:L) (a u0 u1:Ω):
   poleOrder v.val (T.eval (algebraMap Ω L a)-algebraMap Ω L u0-z*algebraMap Ω L u1) ≤
     coefficientPoleWeight v.val T z:=by
 have ht:=eval_pole_le v.val T z _ (constant_value_le_one Ω L v a)
 have h0:=pole_const_le v.val (constant_value_le_one Ω L v) u0
 have hz:=pole_const_mul_le v.val (constant_value_le_one Ω L v) u1 z
 have hseed:=seedPole_le v.val T z
 have hn:=coefficientPoleWeight_nonneg v.val T z
 have hsub (x y:L):poleOrder v.val (x-y) ≤ max (poleOrder v.val x) (poleOrder v.val y):=by
   simpa only [sub_eq_add_neg,pole_neg] using pole_add_le v.val x (-y)
 exact (hsub _ _).trans (max_le ((hsub _ _).trans (max_le ht (h0.trans hn)))
   (by simpa only [mul_comm] using hz.trans hseed))
variable {K Ω:Type} [Field K] [Field Ω]
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
def CoefficientPoleProfile (w cost:ℕ):Prop:=
 ∀ W:Finset (Place Ω (CoordinateField Ω P)),
   (∑ v∈W,coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w)
     (coordinate Ω P 2)) ≤ (cost:ℤ)
theorem coefficientPoleProfile_of_unitYZ_bound (w cost:ℕ)
   (hcoeff:∀ (v:Place Ω (CoordinateField Ω P)) (j:ℕ),
     poleOrder v.val ((truncatedPolynomial φ P F hF hH w).coeff j) ≤
       poleOrder v.val (coordinate Ω P 0))
   (hyz:∀ W:Finset (Place Ω (CoordinateField Ω P)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω P) (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile φ P F hF hH w cost:=by
 have hp (v:Place Ω (CoordinateField Ω P)):
     coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2) ≤
       max (poleOrder v.val (coordinate Ω P 0)) (poleOrder v.val (coordinate Ω P 2)):=by
   unfold coefficientPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (le_max_left _ _).trans (le_max_left _ _)
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact le_max_right _ _
   obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hz
   exact (hcoeff v j).trans (le_max_left _ _)
 intro W
 exact (Finset.sum_le_sum (fun v _↦hp v)).trans
   (by simpa only [exponentSetPoleWeight_unitYZ] using hyz W)
theorem normalized_agreement_eq (w:ℕ) (x u0 u1:K):
   coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
     (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)=
   (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)-
     componentCoefficients φ P u0-coordinate Ω P 2*componentCoefficients φ P u1:=by
 have hclear:=eval_factorial_agreementNumerator (componentCoefficients φ P) F
   (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)
   w x u0 u1
 rw [component_evaluation] at hclear
 have hbase:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) (polyH K F)=
     coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)):=by
   exact component_evaluation φ P _
 rw [hbase,←globalPolynomial_eval] at hclear
 have hz:componentPoint φ P (3:Fin 4)=coordinate Ω P 2:=rfl
 rw [hz] at hclear
 have hne:coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
   rw [←component_evaluation]
   exact component_regular φ P F hH
 apply (div_eq_iff (pow_ne_zero _ hne)).mpr
 simpa only [agreementPolynomial,truncatedPolynomial,mul_comm] using hclear
theorem agreement_regular_zero_le [IsAlgClosed Ω] (base:SeparableLiteralCoordinate P)
   (w cost:ℕ) (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
   (x u0 u1:K) (hproper:agreementPolynomial φ F w x u0 u1∉P):
   FiniteRegularZeroSetBound P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
     (agreementPolynomial φ F w x u0 u1) cost:=by
 apply finite_regular_zero_bound_of_separator Ω P base _ _ (2*w) cost hproper hH
 intro W
 have hlocal (v:Place Ω (CoordinateField Ω P)):
     poleOrder v.val (coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
       (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)) ≤
     coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2):=by
   rw [normalized_agreement_eq φ P F hF hH]
   exact affine_eval_pole_le v _ _ (φ (Polynomial.C x)) (φ (Polynomial.C u0)) (φ (Polynomial.C u1))
 simpa only [RCN346.poleOrder,coordinateEvaluation_eq_aeval] using
   (Finset.sum_le_sum (fun v _↦hlocal v)).trans (hprofile W)
end
end ProximityPrize.SubmissionLower.RCN063
end PackedLegacy_A8

/-! Packed from ProximityPrize.SubmissionLower.BK. -/
section PackedLegacy_BK
namespace ProximityPrize.SubmissionLower.RCN144
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN220 RCN083 RCN228 RCN127 RCN058 RCN063 RCN065 RCN238 RCN243 RCN264 RCN231 RCN229 RCN126 RCN062 RCN047 RCN139 RCN174 RCN114 RCN295 RCN095 RCN275 RCN319 RCN002
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN144.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN144.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
variable {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
theorem stage_surface_mem
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F)):
   surfaceMap (polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨A,hA⟩:=S.G_dvd_surface
 rw [hA]
 exact C.1.mul_mem_right A
   (regularComponent_G_mem (Ω K) S.G _ _ C)
theorem stage_regularity_not_mem
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F)):
   surfaceMap (polynomialEmbedding K) (polyH K S.F)∉C.1:=
 regularComponent_H_not_mem (Ω K) S.G _ _ C
theorem coefficientPoleProfile_of_regular_agreement_curve
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F))
   (bound seedCap slopeCap cost:ℕ)
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hyz:∀ W:Finset (RCN346.Place (Ω K) (CoordinateField (Ω K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S x0 u0 u1 C)
     (stage_regularity_not_mem S x0 u0 u1 C) w cost:=by
 classical
 let φ:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Ω K) Pcurve
 let κ:K →+*L:=componentCoefficients φ Pcurve
 let v0:Fin 4 → L:=componentPoint φ Pcurve
 letI:CharP L p:=
   charP_of_injective_algebraMap (algebraMap (Ω K) L).injective p
 have hFC:=stage_surface_mem S x0 u0 u1 C
 have hHC:=stage_regularity_not_mem S x0 u0 u1 C
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hGQ,hGH0,hTail0⟩:=
   exists_original_factor_with_first_tail S hTail
 have hF0mem:surfaceMap φ F0∈Pcurve:=by
   obtain ⟨A,hA⟩:=hGF0
   rw [hA]
   exact Pcurve.mul_mem_right A (regularComponent_G_mem (Ω K) S.G _ _ C)
 have hHdecomp:surfaceMap φ (polyH K S.F)=
     surfaceMap φ (polyH K F0)*surfaceMap φ Q+
       surfaceMap φ F0*surfaceMap φ (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap φ (polyH K F0)*surfaceMap φ Q∉Pcurve:=by
   intro hm
   apply hHC
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0mem)
 have hQnot:surfaceMap φ Q∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap φ (polyH K F0)∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_right _ h)
 have hF0rel:MvPolynomial.eval₂Hom κ v0 F0=0:=
   (component_evaluation_zero_iff φ Pcurve F0).mpr hF0mem
 have hF0reg:MvPolynomial.eval₂Hom κ v0 (polyH K F0)≠0:=
   (component_evaluation_zero_iff φ Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom κ v0 Q≠0:=
   (component_evaluation_zero_iff φ Pcurve Q).not.mpr hQnot
 have hprodrel:MvPolynomial.eval₂Hom κ v0 (F0*Q)=0:=by
   rw [map_mul,hF0rel,zero_mul]
 have hprodreg:MvPolynomial.eval₂Hom κ v0 (polyH K (F0*Q))≠0:=by
   rw [←hprod]
   exact component_regular φ Pcurve S.F hHC
 let P0:Polynomial L:=globalPolynomial κ F0 v0 hF0rel hF0reg w
 have hP0deg:P0.natDegree≤w:=globalPolynomial_natDegree_le κ F0 v0 hF0rel hF0reg w
 have hSne:S.F≠0:=by
   intro hz
   apply S.regular_proper
   rw [hz]
   simp
 have hF0box:F0∈globalCoefficientBox K bound w seedCap slopeCap:=by
   apply RCN081.mem_globalCoefficientBox_of_dvd F0 S.F bound w seedCap slopeCap
     hSne ⟨Q,hprod⟩ hbox
 have hP0solution:specialization L P0 (v0 3) (MvPolynomial.map κ F0)=0:=
   canonical_polynomiality_of_first_tail κ F0 v0 hF0rel hF0reg
     p bound w seedCap slopeCap hw hshort hchar hF0box hTail0
 have hcanon:truncatedPolynomial φ Pcurve S.F hFC hHC w=P0:=by
   unfold truncatedPolynomial
   change globalPolynomial κ S.F v0 _ _ w=P0
   have hm:=globalPolynomial_mul_factor κ F0 Q v0 hF0rel hQeval hF0reg
     hprodrel hprodreg w
   simpa only [hprod,P0] using hm
 have hagree:P0.eval (κ x0)=κ u0+v0 3*κ u1:=by
   have hm:=regularComponent_T_mem (Ω K) S.G
     (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F) C
   have hv:=(agreement_mem_iff_truncated_value φ Pcurve S.F hFC hHC
     w x0 u0 u1).mp (by simpa only [agreementPolynomial] using hm)
   rw [hcanon] at hv
   change P0.eval (componentCoefficients φ Pcurve x0)=
     componentCoefficients φ Pcurve u0+
       coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1 at hv
   change P0.eval (componentCoefficients φ Pcurve x0)=
     componentCoefficients φ Pcurve u0+
       coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1
   exact hv
 let A0:=agreementNumerator F0 w (fun j => (j.factorial:K)⁻¹) x0 u0 u1
 have hA0proper:¬F0∣A0:=by
   apply RCN220.original_factor_agreement_proper
     φ F0 Q S.G hGF0 w _ x0 u0 u1
   simpa only [agreementPolynomial,hprod] using hproper
 have hvpoint:polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
   · exact globalPolynomial_initial_slope κ F0 v0 hF0rel hF0reg w hw
   · rfl
 have hregspec:specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom,
       RingHom.id_comp] using hF0reg
   intro hz
   apply hmapped
   rw [←hvpoint]
   rw [eval_polynomialPoint_eq_specialization,hz]
   simp
 have hA0solution:specialization L P0 (v0 3) (MvPolynomial.map κ A0)=0:=by
   apply RatFunc.algebraMap_injective L
   rw [map_zero,←fresh_eval_eq]
   rw [map_agreementNumerator_base]
   have hfresh:MvPolynomial.eval₂Hom (algebraMap L (RatFunc L))
       (freshPoint P0 (v0 3))
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     rw [fresh_eval_eq]
     exact RatFunc.algebraMap_ne_zero hregspec
   have heval:=(factorial_agreement_zero_iff_original_agreement
     (algebraMap L (RatFunc L)) (MvPolynomial.map κ F0) P0 (v0 3) RatFunc.X
     hP0solution hfresh p w S.characteristic_bound
     hP0deg (κ x0) (κ u0) (κ u1)).mpr hagree
   simpa only [freshPoint,map_inv₀,map_natCast] using heval
 have htrK:Algebra.trdeg K (baseCoefficientField (k:=K) P0 (v0 3))≤1:=
   baseCoefficientField_trdeg_le_one_of_fresh_proper_relations F0 A0 P0 (v0 3)
     hF0irr hF0pos hA0proper hP0solution hA0solution hregspec
     p w S.characteristic_bound hP0deg
 let k:=algebraicClosure K (Ω K)
 have htrk:Algebra.trdeg k (baseCoefficientField (k:=k) P0 (v0 3))≤1:=
   baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply polynomialEmbedding_injective K
   change f.eval₂ (coefficientEmbedding K) (initialCoordinate K)=
     g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
   rw [generic_eval_eq,generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (initialCoordinate K):=hxK.algebraicClosure
 apply coefficientPoleProfile_of_unitYZ_bound φ Pcurve S.F hFC hHC w cost
 · intro place j
   rw [hcanon]
   apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
     (initialCoordinate K) hxk (coordinate (Ω K) Pcurve 0)
   exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
 · exact hyz
end
end ProximityPrize.SubmissionLower.RCN144
end PackedLegacy_BK

/-! Packed from ProximityPrize.SubmissionLower.BL. -/
section PackedLegacy_BL
namespace ProximityPrize.SubmissionLower.RCN145
open scoped Classical BigOperators
open RCN002 RCN136 RCN231 RCN319 RCN238 RCN065 RCN271 RCN063 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN145.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN145.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem prime_curve_card_le_of_coefficientPoleProfile
   (base:SeparableLiteralCoordinate P) (p w a e cost:ℕ) [CharP Ω p]
   (hchar:w < p) (hwa:w < a) (hcost:1 ≤ cost)
   (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
   (selected:K → Polynomial K) (Γ:Finset K)
   {ι:Type*} (nodes:Finset ι) (x u0 u1:ι → K) (hinj:Set.InjOn x nodes)
   (hsize:nodes.card=a+e)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,a ≤ (nodes.filter (fun i↦
     (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):Γ.card ≤ (e+1)*cost:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let I:=identityNodes φ P F nodes x u0 u1 w
 let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u0 i+γ*u1 i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ cost:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u0 i) (u1 i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le_of_regular_zero_bound φ P F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u0 i) (u1 i) cost
       (agreement_regular_zero_le φ P F hF hH base w cost hprofile _ _ _ hproper)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w cost
     (identityNodes_subset φ P F nodes x u0 u1 w) hI hwa (by omega) hagreement hfiber
   have hg:0 < a-w:=Nat.sub_pos_of_lt hwa
   have hu:nodes.card-w ≤ (e+1)*(a-w):=by
     have he:=Nat.mul_le_mul_left e (show 1 ≤ a-w by omega)
     calc
       nodes.card-w=(a-w)+e:=by omega
       _ ≤ (a-w)+e*(a-w):=by simpa only [Nat.mul_one] using Nat.add_le_add_left he (a-w)
       _=_:=by ring
   have hscaled:Γ.card*(a-w) ≤ ((e+1)*cost)*(a-w):=by
     calc
       _ ≤ (nodes.card-w)*cost:=hcount
       _ ≤ ((e+1)*(a-w))*cost:=Nat.mul_le_mul_right cost hu
       _=_:=by ring
   exact Nat.le_of_mul_le_mul_right hscaled hg
 · have hi:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u0 u1 p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ P F hF hH nodes x u0 u1 w hinj hi
     (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
     (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P0+Polynomial.C γ*P1)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hsmall:Γ.card ≤ e+1:=by
     simpa only [hfilter] using hnoPencil P0 P1 h0 h1
   exact hsmall.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e+1) hcost)
end
end ProximityPrize.SubmissionLower.RCN145
end PackedLegacy_BL

/-! Packed from ProximityPrize.SubmissionLower.GM. -/
section PackedLegacy_GM
namespace ProximityPrize.SubmissionLower.RCN312
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN264 RCN074 RCN086 RCN330 RCN065 RCN238 RCN243 RCN231 RCN139 RCN047 RCN137 RCN082 RCN083 RCN258 RCN217 RCN127 RCN126 RCN062 RCN058 RCN063 RCN145 RCN339 RCN095 RCN237 RCN295 RCN174 RCN319 RCN341 RCN046 RCN042 RCN344 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN312.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN312.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p errors w:ℕ}
 [CharP (Omega K) p]
 {flag tailFlag1:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
theorem firstTailComponent_surface_mem
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 rw [hQ]
 exact C.1.mul_mem_right Q
   (regularComponent_G_mem (Omega K) S.G _ _ C)
theorem firstTailComponent_regularity_not_mem
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K) (polyH K S.F)∉C.1:=
 regularComponent_H_not_mem (Omega K) S.G _ _ C
theorem exists_original_factor_of_firstTailComponent
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   ∃ F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧
     S.G∣surfaceMap (polynomialEmbedding K) F0∧
     surfaceMap (polynomialEmbedding K) F0∈C.1∧
     surfaceMap (polynomialEmbedding K) Q∉C.1∧
     surfaceMap (polynomialEmbedding K) (polyH K F0)∉C.1:=by
 classical
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Omega K) Pcurve
 let phiC:Polynomial K →+*L:=
   (algebraMap (Omega K) L).comp phi
 let vC:Fin 3 → L:=fun i => componentPoint phi Pcurve i.succ
 have hSne:S.F≠0:=by
   intro hzero
   apply S.regular_proper
   rw [hzero]
   simp
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap phiC S.F)=0:=by
   rw [eval_surfaceMap]
   change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
     (componentPoint phi Pcurve) S.F=0
   exact (component_evaluation_zero_iff phi Pcurve S.F).mpr
     (firstTailComponent_surface_mem S C)
 have hphiC:Function.Injective phiC:=
   (algebraMap (Omega K) L).injective.comp (polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=
   exists_active_factor_of_surface_zero phiC hphiC S.F hSne vC hsurfaceZero
 have hF0spec:=activeFactors_spec S.F F0 hF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hF0curve:surfaceMap phi F0∈Pcurve:=by
   rw [←coordinateEvaluation_ker (Omega K) Pcurve]
   rw [eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
     (componentPoint phi Pcurve) F0=0 at hF0zero
   rw [component_evaluation] at hF0zero
   exact hF0zero
 have hHdecomp:surfaceMap phi (polyH K S.F)=
     surfaceMap phi (polyH K F0)*surfaceMap phi Q+
       surfaceMap phi F0*surfaceMap phi (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap phi (polyH K F0)*surfaceMap phi Q∉Pcurve:=by
   intro hm
   apply firstTailComponent_regularity_not_mem S C
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0curve)
 have hQnot:surfaceMap phi Q∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap phi (polyH K F0)∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_right _ h)
 have hGprod:S.G∣surfaceMap phi F0*surfaceMap phi Q:=by
   simpa only [←map_mul, ←hprod] using S.G_dvd_surface
 have hGsplit:=S.irreducible_G.prime.dvd_or_dvd hGprod
 have hGQfalse:¬ S.G∣surfaceMap phi Q:=by
   intro hGQ
   apply hQnot
   exact Pcurve.mem_of_dvd hGQ
     (regularComponent_G_mem (Omega K) S.G _ _ C)
 have hGF0:S.G∣surfaceMap phi F0:=hGsplit.resolve_right hGQfalse
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGF0,
   hF0curve,hQnot,hH0not⟩
theorem original_factor_firstTail_proper
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
   (F0 Q:MvPolynomial (Fin 4) K) (hprod:S.F=F0*Q)
   (hGF0:S.G∣surfaceMap (polynomialEmbedding K) F0):
   ¬ F0∣numerator K F0 (w+1):=by
 intro hdiv
 let phi:=polynomialEmbedding K
 have hscaled:S.G∣surfaceMap phi
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   exact hGF0.trans (map_dvd (surfaceMap phi)
     (dvd_mul_of_dvd_right hdiv (Q^(2*(w+1)))))
 have hdiff:S.G∣surfaceMap phi
     (numerator K (F0*Q) (w+1)-
       Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGF0.trans (map_dvd (surfaceMap phi)
     (factor_dvd_numerator_sub_power F0 Q (w+1)))
 have hwhole:S.G∣surfaceMap phi (numerator K S.F (w+1)):=by
   rw [hprod]
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using
     dvd_add hdiff hscaled
 apply hfirstProper
 exact (globalTailCut_dvd_iff phi (polynomialEmbedding_injective K)
   S.F (w+1) S.G).mpr hwhole
theorem tangent_truncatedPolynomial_solution
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (bound seedCap slopeCap:ℕ) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1):
   specialization (CoordinateField (Omega K) C.1)
     (truncatedPolynomial (polynomialEmbedding K) C.1 S.F
       (firstTailComponent_surface_mem S C)
       (firstTailComponent_regularity_not_mem S C) w)
     (coordinate (Omega K) C.1 2)
     (MvPolynomial.map (componentCoefficients (polynomialEmbedding K) C.1) S.F)=0:=by
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let coefficients:=componentCoefficients phi Pcurve
 let v:=componentPoint phi Pcurve
 let hF:=firstTailComponent_surface_mem S C
 let hH:=firstTailComponent_regularity_not_mem S C
 let hrel:=component_relation phi Pcurve S.F hF
 let hreg:=component_regular phi Pcurve S.F hH
 letI:CharP (CoordinateField (Omega K) Pcurve) p:=
   charP_of_injective_algebraMap
     (algebraMap (Omega K) (CoordinateField (Omega K) Pcurve)).injective p
 apply global_polynomiality_of_all_tails coefficients S.F v hrel hreg
   p bound w seedCap slopeCap hw hshort hchar hbox
 apply (all_tail_numerators_iff_all_tail_jets coefficients S.F v hrel hreg
   p bound w hchar).mp
 intro j hj _
 have hjbase:w+1 ≤ j:=by omega
 have hT:=hallTails (j-(w+1))
 have heq:w+1+(j-(w+1))=j:=Nat.add_sub_of_le hjbase
 rw [heq] at hT
 have hN:surfaceMap phi (numerator K S.F j)∈Pcurve:=
   (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
     S.F j Pcurve).mp hT
 exact (component_evaluation_zero_iff phi Pcurve _).mpr hN
theorem coefficientPoleProfile_of_tangent_firstTail
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣
     globalTailCut (polynomialEmbedding K) S.F (w+1))
   (bound seedCap slopeCap cost:ℕ) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
       (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
     (firstTailComponent_surface_mem S C)
     (firstTailComponent_regularity_not_mem S C) w cost:=by
 classical
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Omega K) Pcurve
 let kappa:K →+*L:=componentCoefficients phi Pcurve
 let v0:Fin 4 → L:=componentPoint phi Pcurve
 let hFC:=firstTailComponent_surface_mem S C
 let hHC:=firstTailComponent_regularity_not_mem S C
 let P0:Polynomial L:=truncatedPolynomial phi Pcurve S.F hFC hHC w
 letI:CharP L p:=charP_of_injective_algebraMap
   (algebraMap (Omega K) L).injective p
 have hP0deg:P0.natDegree ≤ w:=
   truncatedPolynomial_natDegree_le phi Pcurve S.F hFC hHC w
 have hSsolution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa S.F)=0:=
   tangent_truncatedPolynomial_solution S C bound seedCap slopeCap hw
     hshort hchar hbox hallTails
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hF0curve,hQnot,hH0not⟩:=
   exists_original_factor_of_firstTailComponent S C
 have hF0rel:MvPolynomial.eval₂Hom kappa v0 F0=0:=
   (component_evaluation_zero_iff phi Pcurve F0).mpr hF0curve
 have hF0regPoint:MvPolynomial.eval₂Hom kappa v0 (polyH K F0)≠0:=
   (component_evaluation_zero_iff phi Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom kappa v0 Q≠0:=
   (component_evaluation_zero_iff phi Pcurve Q).not.mpr hQnot
 have hvpoint:polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
   · exact truncatedPolynomial_initial_slope phi Pcurve S.F hFC hHC w hw
   · rfl
 have hQsolution_ne:specialization L P0 (v0 3)
     (MvPolynomial.map kappa Q)≠0:=by
   intro hz
   apply hQeval
   calc
     MvPolynomial.eval₂Hom kappa v0 Q=
         MvPolynomial.eval₂Hom (RingHom.id L)
           (polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0))
           (MvPolynomial.map kappa Q):=by
       rw [hvpoint,MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
     _=(specialization L P0 (v0 3)
         (MvPolynomial.map kappa Q)).eval (v0 0):=by
       simpa using eval_polynomialPoint_eq_specialization
         (RingHom.id L) P0 (v0 3) (v0 0) (MvPolynomial.map kappa Q)
     _=0:=by rw [hz];simp
 have hF0solution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa F0)=0:=by
   have hmul:specialization L P0 (v0 3) (MvPolynomial.map kappa F0)*
       specialization L P0 (v0 3) (MvPolynomial.map kappa Q)=0:=by
     simpa only [hprod,map_mul] using hSsolution
   exact (mul_eq_zero.mp hmul).resolve_right hQsolution_ne
 have hF0reg:specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,
       MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp] using hF0regPoint
   intro hz
   apply hmapped
   rw [←hvpoint,eval_polynomialPoint_eq_specialization,hz]
   simp
 have hTsolution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa (numerator K F0 (w+1)))=0:=by
   rw [map_numerator]
   exact specialization_numerator_zero_of_degree L (MvPolynomial.map kappa F0)
     P0 (v0 3) hF0solution (w+1) (hP0deg.trans_lt (by omega))
 have hTproper:¬ F0∣numerator K F0 (w+1):=
   original_factor_firstTail_proper S hfirstProper F0 Q hprod hGF0
 have htrK:Algebra.trdeg K (baseCoefficientField (k:=K) P0 (v0 3)) ≤ 1:=
   baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
     F0 (numerator K F0 (w+1)) P0 (v0 3)
     hF0irr hF0pos hTproper hF0solution hTsolution hF0reg
     p w S.characteristic_bound hP0deg
 let k:=algebraicClosure K (Omega K)
 have htrk:Algebra.trdeg k (baseCoefficientField (k:=k) P0 (v0 3)) ≤ 1:=
   baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply polynomialEmbedding_injective K
   change f.eval₂ (coefficientEmbedding K) (initialCoordinate K)=
     g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
   rw [generic_eval_eq,generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (initialCoordinate K):=hxK.algebraicClosure
 apply coefficientPoleProfile_of_unitYZ_bound phi Pcurve S.F hFC hHC w cost
 · intro place j
   apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
     (initialCoordinate K) hxk (coordinate (Omega K) Pcurve 0)
   exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
 · exact hyz
theorem tangent_component_card_le
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣
     globalTailCut (polynomialEmbedding K) S.F (w+1))
   (base:SeparableLiteralCoordinate C.1)
   (agreements bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=agreements+errors)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreements) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w+1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (hyzPositive:1 ≤ B.yzCost C)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
       (flagSupport unitYZFlag)) ≤ (B.yzCost C:ℤ)):
   (componentSeeds (Omega K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w+1))
     (regularitySurface (polynomialEmbedding K) S.F) Gamma
     (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
       (errors+1)*B.yzCost C:=by
 classical
 let T1:=globalTailCut (polynomialEmbedding K) S.F (w+1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let Gc:=componentSeeds (Omega K) S.G T1 H Gamma
   (selectedPoint (polynomialEmbedding K) S.selected) C
 have hGcGamma:Gc ⊆ Gamma:=
   componentSeeds_subset (Omega K) S.G T1 H Gamma _ C
 have hprofile:=coefficientPoleProfile_of_tangent_firstTail
   S C hfirstProper bound seedCap slopeCap (B.yzCost C) hw hshort hchar
   hbox hallTails hyz
 apply prime_curve_card_le_of_coefficientPoleProfile
   (polynomialEmbedding K) C.1 S.F
   (firstTailComponent_surface_mem S C)
   (firstTailComponent_regularity_not_mem S C)
   base p w agreements errors (B.yzCost C)
   S.characteristic_bound hwa hyzPositive hprofile
   S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
 · intro gamma hgamma
   exact S.degree_le gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.solution gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.regular gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact componentSeeds_on_prime (Omega K) S.G T1 H Gamma
     (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
 · intro gamma hgamma
   have hGamma:=hGcGamma hgamma
   simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
     hagreement gamma hGamma
 · exact noLargeSelectedPencil_mono S.selected Gamma Gc w errors
     hGcGamma S.no_large_pencil
end
end ProximityPrize.SubmissionLower.RCN312
end PackedLegacy_GM

/-! Packed from ProximityPrize.SubmissionLower.GZ. -/
section PackedLegacy_GZ
namespace ProximityPrize.SubmissionLower.RCN329
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN046 RCN341 RCN002 RCN344 RCN312 RCN338 RCN174 RCN042 RCN339
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN329.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN329.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p:ℕ}
 [CharP (Omega K) p] {flag:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
end
end ProximityPrize.SubmissionLower.RCN329
end PackedLegacy_GZ

/-! Packed from ProximityPrize.SubmissionLower.FG. -/
section PackedLegacy_FG
namespace ProximityPrize.SubmissionLower.RCN219
open scoped Classical TensorProduct
open RCN135 RCN136 RCN072 RCN264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
abbrev Omega (K:Type) [Field K]:=GenericField K
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
abbrev Collected (K:Type) [Field K]:=
 MvPolynomial (Fin 3) (Polynomial K)
abbrev GenericPoly3 (K:Type) [Field K]:=
 MvPolynomial (Fin 3) (Omega K)
local instance _root_.ProximityPrize.SubmissionLower.RCN219.instAlgebraPolynomialOmega :Algebra (Polynomial K) (Omega K):=
 (polynomialEmbedding K).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN219.instIsTorsionFreePolynomialOmega :Module.IsTorsionFree (Polynomial K) (Omega K):=
 (Module.isTorsionFree_iff_algebraMap_injective).2
   (polynomialEmbedding_injective K)
local instance _root_.ProximityPrize.SubmissionLower.RCN219.instFlatPolynomialOmega :Module.Flat (Polynomial K) (Omega K):=inferInstance
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra
local instance genericPolynomial_flat:
   Module.Flat (Collected K) (GenericPoly3 K):=by
 let E:=Algebra.IsPushout.equiv (Polynomial K) (Collected K)
   (Omega K) (GenericPoly3 K)
 letI:Module.Flat (Collected K)
     ((Collected K) ⊗[Polynomial K] Omega K):=inferInstance
 exact Module.Flat.of_linearEquiv E.symm.toLinearEquiv
def collectedPrime (P:Ideal (GenericPoly3 K)):Ideal (Collected K):=
 P.comap (algebraMap (Collected K) (GenericPoly3 K))
def originalPrime (P:Ideal (GenericPoly3 K)):Ideal (Poly4 K):=
 (collectedPrime P).comap (collectX K).toRingEquiv
theorem mem_originalPrime_iff
   (P:Ideal (GenericPoly3 K)) (A:Poly4 K):
   A∈originalPrime P ↔
     surfaceMap (polynomialEmbedding K) A∈P:=by
 rfl
instance collectedPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (collectedPrime P).IsPrime:=
 Ideal.IsPrime.comap (algebraMap (Collected K) (GenericPoly3 K))
instance originalPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (originalPrime P).IsPrime:=
 Ideal.IsPrime.comap (collectX K).toRingEquiv
theorem collectedPrime_height_le
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (collectedPrime P).height ≤ P.height:=by
 let p:=collectedPrime P
 letI:p.IsPrime:=inferInstance
 letI:P.LiesOver p:=⟨rfl⟩
 have h:=Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
 rw [h]
 exact le_add_right (le_refl _)
theorem originalPrime_height_le
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (originalPrime P).height ≤ P.height:=by
 calc
   (originalPrime P).height=(collectedPrime P).height:=by
     simpa only [originalPrime] using
       RingEquiv.height_comap (collectX K).toRingEquiv (collectedPrime P)
   _ ≤ P.height:=collectedPrime_height_le P
theorem originalPrime_height_eq_two
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]
   (hPheight:P.height ≤ 2)
   (F N:Poly4 K) (hF:Irreducible F)
   (hFmem:surfaceMap (polynomialEmbedding K) F∈P)
   (hNmem:surfaceMap (polynomialEmbedding K) N∈P)
   (hproper:¬ F∣N):
   (originalPrime P).height=2:=by
 let p:=originalPrime P
 let I:Ideal (Poly4 K):=Ideal.span {F}
 letI:p.IsPrime:=inferInstance
 letI:I.IsPrime:=Ideal.isPrime_span_singleton_of_prime hF.prime
 have hFmem':F∈p:=(mem_originalPrime_iff P F).2 hFmem
 have hNmem':N∈p:=(mem_originalPrime_iff P N).2 hNmem
 have hIp:I ≤ p:=by
   apply Ideal.span_le.2
   simpa using hFmem'
 have hNnot:N∉I:=by
   intro h
   exact hproper (Ideal.mem_span_singleton.mp h)
 have hIne:I≠p:=by
   intro h
   exact hNnot (h ▸ hNmem')
 have hIlt:I < p:=lt_of_le_of_ne hIp hIne
 have hIbot:I≠⊥:=by
   intro h
   have hzero:F=0:=by
     have:F∈(⊥:Ideal (Poly4 K)):=h ▸ Ideal.subset_span (by simp)
     simpa using this
   exact hF.ne_zero hzero
 have hbotlt:(⊥:Ideal (Poly4 K)) < I:=
   lt_of_le_of_ne bot_le hIbot.symm
 have hone:(1:ℕ∞) ≤ I.height:=by
   calc
     1=(0:ℕ∞)+1:=by simp
     _ ≤ (⊥:Ideal (Poly4 K)).height+1:=by gcongr;exact zero_le
     _ ≤ I.height:=Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
 have htwo:(2:ℕ∞) ≤ p.height:=by
   calc
     2=(1:ℕ∞)+1:=by norm_num
     _ ≤ I.height+1:=by gcongr
     _ ≤ p.height:=Ideal.height_add_one_le_of_lt_of_isPrime hIlt
 exact le_antisymm ((originalPrime_height_le P).trans hPheight) htwo
end
end ProximityPrize.SubmissionLower.RCN219
end PackedLegacy_FG

/-! Packed from ProximityPrize.SubmissionLower.AL. -/
section PackedLegacy_AL
namespace ProximityPrize.SubmissionLower.RCN327
open ProximityPrize.Benchmark RCN095 RCN275 RCN198 RCN206 RCN263
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def w:ℕ:=131071
def errors:ℕ:=80102
namespace Profile
end Profile
end
end ProximityPrize.SubmissionLower.RCN327
end PackedLegacy_AL

/-! Packed from ProximityPrize.SubmissionLower.FT. -/
section PackedLegacy_FT
namespace ProximityPrize.SubmissionLower.RCN244
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN329 RCN312 RCN219 RCN218 RCN073 RCN086 RCN330 RCN328 RCN237 RCN095 RCN198 RCN287 RCN313 RCN217 RCN243 RCN072 RCN238
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN244.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN244.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
abbrev fixedSupport:=support 1206 42 10
abbrev Stage (K I:Type) [Field K]
   (Gamma:Finset K) (x:I → K) (p:ℕ) [CharP (GenericField K) p]
   (flag:FlagDegree)
   (errorCap:ℕ:=RCN327.errors)
   (stageSupport:RCN275.ResidualSupportParameters:=fixedSupport):=
 ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag
   RCN326.w stageSupport
variable {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
structure OriginalData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) where
 factor:MvPolynomial (Fin 4) K
 cofactor:MvPolynomial (Fin 4) K
 irreducible:Irreducible factor
 positive:0 < factor.degreeOf 1+factor.degreeOf 2+factor.degreeOf 3
 product:S.F=factor*cofactor
 factor_dvd:S.G∣surfaceMap (polynomialEmbedding K) factor
 factor_mem:surfaceMap (polynomialEmbedding K) factor∈C.1
 cofactor_not_mem:surfaceMap (polynomialEmbedding K) cofactor∉C.1
 regularity_not_mem:
   surfaceMap (polynomialEmbedding K) (polyH K factor)∉C.1
noncomputable def originalData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   OriginalData S C:=by
 let h:=exists_original_factor_of_firstTailComponent S C
 let factor:=h.choose
 let cofactor:=h.choose_spec.choose
 have hs:=h.choose_spec.choose_spec
 exact ⟨factor,cofactor,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
   hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩
abbrev componentPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 contractedPrime (polynomialEmbedding K) C.1
theorem factorLe
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   RCN218.factorIdeal (originalData S C).factor ≤ componentPrime S C:=
 RCN218.factorIdeal_le_contractedPrime (polynomialEmbedding K) C.1
   (originalData S C).factor (originalData S C).factor_mem
abbrev LocalRing
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 FactorLocal (originalData S C).factor (componentPrime S C) (factorLe S C)
local instance factorIdealPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN218.factorIdeal (originalData S C).factor).IsPrime:=
 RCN218.factorIdeal_isPrime _ (originalData S C).irreducible
local instance quotientPrimeInstance
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN186.quotientPrime
     (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).IsPrime:=
 RCN186.quotientPrime_isPrime _ _ (factorLe S C)
noncomputable def localImage
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):LocalRing S C:=
 factorLocalImage (originalData S C).factor (componentPrime S C)
   (factorLe S C) A
noncomputable def localDerivation
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   Derivation K (LocalRing S C) (LocalRing S C):=
 factorLocalDerivation (originalData S C).factor (componentPrime S C)
   (factorLe S C)
theorem original_firstNumerator_mem_component
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K)
     (numerator K (originalData S C).factor
       (RCN326.w+1))∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 let b:=RCN326.w+1
 have hwhole:surfaceMap phi (numerator K S.F b)∈C.1:=by
   apply (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
     S.F b C.1).mp
   exact regularComponent_T_mem (GenericField K) S.G
     (globalTailCut phi S.F b) (regularitySurface phi S.F) C
 have hdiff:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hdiffMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   exact C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hdiff))
     d.factor_mem
 have hproduct:surfaceMap phi
     (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   have:=C.1.sub_mem hwhole hdiffMap
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
 have hproduct':surfaceMap phi (d.cofactor^(2*b))*
     surfaceMap phi (numerator K d.factor b)∈C.1:=by
   simpa only [map_mul] using hproduct
 have hsplit:surfaceMap phi (d.cofactor^(2*b))∈C.1∨
     surfaceMap phi (numerator K d.factor b)∈C.1:=
   (inferInstance:C.1.IsPrime).mem_or_mem hproduct'
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rcases hsplit with hleft | hright
 · exact False.elim (hcofactorPow (by simpa only [map_pow] using hleft))
 · exact hright
theorem componentPrime_height_eq_two
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   (componentPrime S C).height=2:=by
 let d:=originalData S C
 let N:=numerator K d.factor (RCN326.w+1)
 have hproperN:¬ d.factor∣N:=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hheightC:C.1.height ≤ 2:=
   component_height_le_two (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1)) C.1
     (regularComponent_mem (GenericField K) S.G _ _ C)
 have horiginal:=originalPrime_height_eq_two C.1 hheightC d.factor N
   d.irreducible d.factor_mem (original_firstNumerator_mem_component S C) hproperN
 have heq:componentPrime S C=originalPrime C.1:=by
   apply Ideal.ext
   intro A
   exact (mem_contractedPrime_iff (polynomialEmbedding K) C.1 A).trans
     (mem_originalPrime_iff C.1 A).symm
 rw [heq]
 exact horiginal
structure LocalDVRFamily (S:Stage K I Gamma x p flag errorCap stageSupport) where
 domain:∀ C:FirstTailComponent S,IsDomain (LocalRing S C)
 dvr:∀ C:FirstTailComponent S,
   @IsDiscreteValuationRing (LocalRing S C) _ (domain C)
theorem canonicalLocalDVRFamily
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   LocalDVRFamily S where
 domain:=fun C↦inferInstance
 dvr:=fun C↦by
   exact factorLocal_isDiscreteValuationRing
     (originalData S C).factor (componentPrime S C) (factorLe S C)
     (componentPrime_height_eq_two S C hfirstProper)
     (originalData S C).regularity_not_mem
noncomputable def localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S):ℕ:=by
 letI:IsDomain (LocalRing S C):=L.domain C
 letI:IsDiscreteValuationRing (LocalRing S C):=L.dvr C
 exact (IsDiscreteValuationRing.addVal (LocalRing S C)
   (localImage S C (numerator K (originalData S C).factor
     (RCN326.w+1)))).toNat
theorem localImage_isUnit_iff_not_mem
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):
   IsUnit (localImage S C A) ↔
     surfaceMap (polynomialEmbedding K) A∉C.1:=by
 constructor
 · intro hunit hmem
   have hnon:¬ IsUnit (localImage S C A):=by
     change ¬ IsUnit
       (factorLocalImage
         (originalData S C).factor (componentPrime S C) (factorLe S C) A)
     have hmax:=
       (IsLocalization.AtPrime.to_map_mem_maximal_iff
         (LocalRing S C)
         (RCN186.quotientPrime
           (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C))
         (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A)).2 (by
           have:A∈
               (RCN186.quotientPrime
                 (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).comap
                 (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor)):=by
             rw [RCN186.quotientPrime_comap_quotientMk
               (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)
               (factorLe S C)]
             exact hmem
           exact this)
     simpa only [factorLocalImage,IsLocalRing.mem_maximalIdeal,
       mem_nonunits_iff] using hmax
   exact hnon hunit
 · intro hnot
   exact factorLocal_image_isUnit_of_not_mem
     (originalData S C).factor A (componentPrime S C) (factorLe S C) hnot
theorem tail_mem_iff_original_numerator_mem
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) (b:ℕ):
   globalTailCut (polynomialEmbedding K) S.F b∈C.1 ↔
     surfaceMap (polynomialEmbedding K)
       (numerator K (originalData S C).factor b)∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 have hscaled:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hscaledMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=
   C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hscaled))
     d.factor_mem
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rw [globalTailCut_mem_iff phi (polynomialEmbedding_injective K) S.F b C.1]
 constructor
 · intro hwhole
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     have:=C.1.sub_mem hwhole hscaledMap
     simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
   have hproduct':surfaceMap phi (d.cofactor^(2*b))*
       surfaceMap phi (numerator K d.factor b)∈C.1:=by
     simpa only [map_mul] using hproduct
   exact ((inferInstance:C.1.IsPrime).mem_or_mem hproduct').resolve_left
     hcofactorPow
 · intro horiginal
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     rw [map_mul]
     exact C.1.mul_mem_left _ horiginal
   have:=C.1.add_mem hscaledMap hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using this
public theorem chosenLocalImage_ne_zero_of_not_dvd
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K)
   (hA:¬ (originalData S C).factor∣A):
   localImage S C A≠0:=by
 intro hzero
 have hquot:Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A=0:=by
   apply (IsLocalization.injective (LocalRing S C)
     (RCN186.quotientPrime
       (RCN218.factorIdeal (originalData S C).factor)
       (componentPrime S C)).primeCompl_le_nonZeroDivisors)
   simpa only [localImage,factorLocalImage,map_zero] using hzero
 exact hA (Ideal.mem_span_singleton.mp
   (Ideal.Quotient.eq_zero_iff_mem.mp hquot))
theorem local_order_tail_dichotomy
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   1 ≤ localMultiplicity S L C∧
     ((∃ delay,1 ≤ delay∧delay ≤ localMultiplicity S L C∧
       globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1+delay)∉C.1)∨
     (∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1)):=by
 let d:=originalData S C
 let p0:=componentPrime S C
 let hFp:=factorLe S C
 let R:=LocalRing S C
 let D:=localDerivation S C
 let H:R:=localImage S C (polyH K d.factor)
 let N:ℕ → R:=fun j↦localImage S C
   (numerator K d.factor (RCN326.w+1+j))
 let coeff:ℕ → R:=fun j↦
   (2*(RCN326.w+1+j):R)
 letI:IsDomain R:=L.domain C
 letI:IsDiscreteValuationRing R:=L.dvr C
 letI:CharP K p:=
   (coefficientEmbedding K).charP (coefficientEmbedding_injective K) p
 letI:CharP R p:=charP_of_injective_algebraMap
   (algebraMap K R).injective p
 have hpne:p≠0:=by
   have:=S.characteristic_bound
   dsimp only [RCN326.w] at this
   omega
 have hp:p.Prime:=CharP.char_prime_of_ne_zero (GenericField K) hpne
 have hproperN:¬ d.factor∣
     numerator K d.factor (RCN326.w+1):=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hN0ne:N 0≠0:=by
   exact chosenLocalImage_ne_zero_of_not_dvd S C _ hproperN
 have hN0nonunit:¬ IsUnit (N 0):=by
   have hmem:=original_firstNumerator_mem_component S C
   exact (localImage_isUnit_iff_not_mem S C _).not.mpr (not_not.mpr hmem)
 have hHunit:IsUnit H:=
   (localImage_isUnit_iff_not_mem S C _).2 d.regularity_not_mem
 have hrec:∀ j,N (j+1)=
     H*D (N j)-coeff j*N j*D H:=by
   intro j
   dsimp only [N,H,D,coeff,d,localImage,localDerivation]
   convert
     (factorLocal_numerator_succ
       (originalData S C).factor (componentPrime S C) (factorLe S C)
       (RCN326.w+1+j)) using 1 <;>
     push_cast <;> ring
 have hd:=recurrence_unit_or_persistent D H (D H) coeff N p hp
   hrec hHunit hN0ne hN0nonunit
 change 1 ≤ localMultiplicity S L C∧_
 change 1 ≤ (IsDiscreteValuationRing.addVal R (N 0)).toNat∧_ at hd
 refine ⟨hd.1,?_⟩
 rcases hd.2 with hproper | hpersistent
 · left
   obtain ⟨delay,hdelay1,hdelayMu,hunit⟩:=hproper
   refine ⟨delay,hdelay1,hdelayMu,?_⟩
   apply (tail_mem_iff_original_numerator_mem S C _).not.mpr
   exact (localImage_isUnit_iff_not_mem S C _).1 hunit
 · right
   intro delay
   by_contra hnot
   apply hpersistent delay
   apply (localImage_isUnit_iff_not_mem S C _).2
   exact (tail_mem_iff_original_numerator_mem S C _).not.mp hnot
theorem one_le_localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   ∀ C,1 ≤ localMultiplicity S
     (canonicalLocalDVRFamily S hfirstProper) C:=by
 intro C
 exact (local_order_tail_dichotomy S
   (canonicalLocalDVRFamily S hfirstProper) C hfirstProper).1
end
end ProximityPrize.SubmissionLower.RCN244
end PackedLegacy_FT

/-! Packed from ProximityPrize.SubmissionLower.GL. -/
section PackedLegacy_GL
namespace ProximityPrize.SubmissionLower.RCN310
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A:Type*} [CommRing A]
theorem exists_multiplier_mem_sup_pow_of_localized_mem
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n):
   ∃ s:A,s∉p∧s*x∈I ⊔ p^n:=by
 let S:=A ⧸ I
 let L:=Localization.AtPrime pbar
 let q:A →+*S:=Ideal.Quotient.mk I
 have hxMap:algebraMap S L (q x)∈
     Ideal.map (algebraMap S L) (pbar^n):=by
   rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal pbar L]
   exact hx
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
   pbar.primeCompl L] at hxMap
 obtain ⟨m,hmM,hmprod⟩:=hxMap
 obtain ⟨s,hs⟩:=Ideal.Quotient.mk_surjective m
 have hcomap:Ideal.comap q pbar=p:=by
   rw [hpbar,Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
     ←RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp]
 have hsnot:s∉p:=by
   intro hsp
   have hqsp:q s∈pbar:=by
     change s∈Ideal.comap q pbar
     rwa [hcomap]
   exact hmM (hs ▸ hqsp)
 have hmprod':q (s*x)∈pbar^n:=by
   simpa only [q,map_mul,hs] using hmprod
 have hmapped:q (s*x)∈Ideal.map q (p^n):=by
   rw [Ideal.map_pow, ←hpbar]
   exact hmprod'
 have hcomapPow:s*x∈Ideal.comap q (Ideal.map q (p^n)):=hmapped
 rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
   ←RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcomapPow
 exact ⟨s,hsnot,by simpa only [sup_comm] using hcomapPow⟩
theorem isPrimary_of_maximal_power_le_le
   (J Q:Ideal A) [J.IsMaximal] (n:ℕ) (hn:1 ≤ n)
   (hpow:J^n ≤ Q) (hle:Q ≤ J):Q.IsPrimary:=by
 apply Ideal.isPrimary_of_isMaximal_radical
 have hrad:Ideal.radical Q=J:=by
   apply le_antisymm
   · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
   · intro x hx
     exact ⟨n,hpow (Ideal.pow_mem_pow hx n)⟩
 rw [hrad]
 exact inferInstance
theorem mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   (surface x s:A) (J:Ideal A) [J.IsMaximal]
   (hsurface:surface∈J) (n:ℕ) (hn:1 ≤ n)
   (hs:s∉J)
   (hmul:s*x∈Ideal.span {surface} ⊔ J^n):
   x∈Ideal.span {surface} ⊔ J^n:=by
 let Q:=Ideal.span {surface} ⊔ J^n
 have hpow:J^n ≤ Q:=le_sup_right
 have hle:Q ≤ J:=by
   exact sup_le (Ideal.span_le.mpr (by simpa))
     (Ideal.pow_le_self (Nat.ne_of_gt hn))
 have hprimary:Q.IsPrimary:=
   isPrimary_of_maximal_power_le_le J Q n hn hpow hle
 have hcases:=(Ideal.isPrimary_iff.mp hprimary).2
   (by simpa only [mul_comm] using hmul)
 rcases hcases with hxQ | hsrad
 · exact hxQ
 · have hrad:Ideal.radical Q=J:=by
     apply le_antisymm
     · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
     · intro y hy
       exact ⟨n,hpow (Ideal.pow_mem_pow hy n)⟩
   exact False.elim (hs (hrad ▸ hsrad))
end
end ProximityPrize.SubmissionLower.RCN310
end PackedLegacy_GL

/-! Packed from ProximityPrize.SubmissionLower.FX. -/
section PackedLegacy_FX
namespace ProximityPrize.SubmissionLower.RCN248
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN248.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN248.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem exists_original_multiplier_for_localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S):
   let d:=originalData S C
   let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
   ∃ s:MvPolynomial (Fin 4) K,
     s∉componentPrime S C∧
     s*numerator K d.factor
       (RCN326.w+1)∈
         RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu:=by
 let d:=originalData S C
 let family:=canonicalLocalDVRFamily S hfirstProper
 let mu:=localMultiplicity S family C
 let N:=numerator K d.factor
   (RCN326.w+1)
 let p0:=componentPrime S C
 let I0:=RCN218.factorIdeal d.factor
 let q0:=quotientPrime I0 p0
 let R:=LocalRing S C
 letI:IsDomain R:=family.domain C
 letI:IsDiscreteValuationRing R:=family.dvr C
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have horder:IsDiscreteValuationRing.addVal R (localImage S C N)=mu:=by
   change IsDiscreteValuationRing.addVal R (localImage S C N)=
     (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat
   apply (ENat.coe_toNat ?_).symm
   intro htop
   change 1 ≤ (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat at hmuPos
   rw [htop] at hmuPos
   simp at hmuPos
 obtain ⟨uniformizer,hUniformizer⟩:=
   IsDiscreteValuationRing.exists_irreducible R
 have hdvd:uniformizer^mu∣localImage S C N:=by
   apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
   rw [hUniformizer.addVal_pow,horder]
 have hxMax:localImage S C N∈IsLocalRing.maximalIdeal R^mu:=by
   rw [hUniformizer.maximalIdeal_eq,Ideal.span_singleton_pow,
     Ideal.mem_span_singleton]
   exact hdvd
 haveI:I0.IsPrime:=RCN218.factorIdeal_isPrime d.factor d.irreducible
 haveI:q0.IsPrime:=quotientPrime_isPrime I0 p0 (factorLe S C)
 exact exists_multiplier_mem_sup_pow_of_localized_mem
   I0 p0 (factorLe S C) q0 rfl N mu hxMax
theorem proper_global_tail_mem_projected_primary
   {B:Type*} [CommRing B]
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S)
   (f:MvPolynomial (Fin 4) K →+*B)
   (surface tail scalar:B) (J:Ideal B) [J.IsMaximal]
   (hfactor:f (originalData S C).factor∈Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=componentPrime S C)
   (htail:tail=f (numerator K S.F
     (RCN326.w+1))*scalar):
   tail∈Ideal.span {surface} ⊔
     J^localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C:=by
 let d:=originalData S C
 let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
 let b:=RCN326.w+1
 let Nfactor:=numerator K d.factor b
 let Q:=Ideal.span {surface} ⊔ J^mu
 obtain ⟨s,hsnot,hsN⟩:=
   exists_original_multiplier_for_localMultiplicity S hfirstProper C
 have hmapI:Ideal.map f (RCN218.factorIdeal d.factor) ≤ Ideal.span {surface}:=by
   rw [RCN218.factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
   exact Set.singleton_subset_iff.mpr hfactor
 have hmapP:Ideal.map f (componentPrime S C) ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (componentPrime S C^mu) ≤ J^mu:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP mu
 have htarget:Ideal.map f
     (RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu) ≤ Q:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f Nfactor∈Q:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsN)
 have hfs:f s∉J:=by
   intro hsJ
   apply hsnot
   rw [←hcontract]
   exact hsJ
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have hNfactor:f Nfactor∈Q:=
   mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
     surface (f Nfactor) (f s) J hsurface mu hmuPos hfs hmul
 have hdiff:d.factor∣numerator K S.F b-
     d.cofactor^(2*b)*Nfactor:=
   factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
     d.product b
 have hdiffMap:f (numerator K S.F b-
     d.cofactor^(2*b)*Nfactor)∈Ideal.span {surface}:=
   (Ideal.span {surface}).mem_of_dvd (map_dvd f hdiff) hfactor
 have hproduct:f (d.cofactor^(2*b)*Nfactor)∈Q:=by
   rw [map_mul]
   exact Q.mul_mem_left _ hNfactor
 have hwhole:f (numerator K S.F b)∈Q:=by
   have hdiffQ:f (numerator K S.F b-
       d.cofactor^(2*b)*Nfactor)∈Q:=
     (show Ideal.span {surface} ≤ Q from le_sup_left) hdiffMap
   have hadd:=Q.add_mem hdiffQ hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using hadd
 rw [htail]
 exact Q.mul_mem_right scalar hwhole
end
end ProximityPrize.SubmissionLower.RCN248
end PackedLegacy_FX

/-! Packed from ProximityPrize.SubmissionLower.FU. -/
section PackedLegacy_FU
namespace ProximityPrize.SubmissionLower.RCN245
open RCN244 RCN135 RCN136 RCN074 RCN095 RCN102 RCN113 RCN120 RCN086 RCN313 RCN002 RCN011 RCN125
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
 {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
abbrev StageComponent (S:Stage K I Gamma x p flag errorCap stageSupport):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
 ((fiberLocalizePlane q hq).comp
   (flagPlaneMap (GenericField K) lam mu nu order)).comp
     (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq
   (flagPlaneMap (GenericField K) lam mu nu order
     (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
       (RCN326.w+1))))
end
end ProximityPrize.SubmissionLower.RCN245
end PackedLegacy_FU

/-! Packed from ProximityPrize.SubmissionLower.FV. -/
section PackedLegacy_FV
namespace ProximityPrize.SubmissionLower.RCN246
open RCN244 RCN248 RCN135 RCN136 RCN095 RCN074 RCN106 RCN107 RCN102 RCN245 RCN113 RCN120 RCN086 RCN264 RCN218 RCN313 RCN002 RCN011 RCN021 RCN125 RCN093
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN246.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN246.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedStageSurface_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageSurfacePlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu S.G))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu S.G)=0
 rw [flagEvaluation_flag]
 change S.G∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_G_mem (GenericField K) S.G _ _ (component a)
structure IndexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):Prop where
 relationMax:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
 factor_mem:stageFiberTargetMap S lam mu nu order q hq
   (originalData S (component a.1)).factor∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)}
 surface_mem:indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)∈
   indexedFiberRelation component lam mu nu order ht q hq a
 contract:(indexedFiberRelation component lam mu nu order ht q hq a).comap
   (stageFiberTargetMap S lam mu nu order q hq)=componentPrime S (component a.1)
 tail_eq:indexedFiberTail q hq (stageTailPlane S lam mu nu order)=
   stageFiberTargetMap S lam mu nu order q hq
     (numerator K S.F (RCN326.w+1))*
       stageFiberScalar S lam mu nu order q hq
theorem indexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   IndexedFiberProjectionData S component lam mu nu order ht q hq a:=by
 let phi:=polynomialEmbedding K
 let plane:=flagPlaneMap (GenericField K) lam mu nu order
 let localize:=fiberLocalizePlane q hq
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 refine ⟨indexedFiberRelation_isMaximal component lam mu nu order ht
   hfinite hgen q hq a,?_,?_,?_,?_⟩
 · rw [Ideal.mem_span_singleton]
   exact map_dvd (localize.comp plane) (originalData S (component a.1)).factor_dvd
 · exact Ideal.mem_map_of_mem localize
     (indexedStageSurface_mem_relation S component lam mu nu order ht a.1)
 · have hplane:(relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap plane=(component a.1).1:=by
     change (relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap
       ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom)=_
     rw [←Ideal.comap_comap,relationKernel_contract,
       flagEvaluation_kernel_contract]
   change J.comap ((localize.comp plane).comp (surfaceMap phi))=
     componentPrime S (component a.1)
   rw [←Ideal.comap_comap, ←Ideal.comap_comap,
     indexedFiberRelation_under,hplane]
   rfl
 · change localize (plane (globalTailCut phi S.F
     (RCN326.w+1)))=
     localize (plane (surfaceMap phi (numerator K S.F
       (RCN326.w+1))))*
       localize (plane (MvPolynomial.C
         ((-phi Polynomial.X)^(RCN326.w+1))))
   rw [globalTailCut_eq,map_mul,map_mul]
end
end ProximityPrize.SubmissionLower.RCN246
end PackedLegacy_FV

/-! Packed from ProximityPrize.SubmissionLower.FW. -/
section PackedLegacy_FW
namespace ProximityPrize.SubmissionLower.RCN247
open RCN244 RCN248 RCN074 RCN106 RCN107 RCN102 RCN245 RCN246 RCN120 RCN086 RCN218 RCN135 RCN313 RCN095 RCN093 RCN002 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN247.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN247.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedFiberTail_mem_primary
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberTail q hq (stageTailPlane S lam mu nu order)∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^
         localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (component a.1):=by
 let D:=indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
 letI:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=
   D.relationMax
 have hfactor:=D.factor_mem
 have hsurface:=D.surface_mem
 have hcontract:=D.contract
 have htail:=D.tail_eq
 apply proper_global_tail_mem_projected_primary
   (K:=K) (I:=I) (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
   (B:=Polynomial (FiberCoefficient q hq))
   (S:=S) (hfirstProper:=hfirstProper) (C:=component a.1)
   (f:=stageFiberTargetMap S lam mu nu order q hq)
   (surface:=indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order))
   (tail:=indexedFiberTail q hq (stageTailPlane S lam mu nu order))
   (scalar:=stageFiberScalar S lam mu nu order q hq)
   (J:=indexedFiberRelation component lam mu nu order ht q hq a)
 · exact hfactor
 · exact hsurface
 · exact hcontract
 · exact htail
end
end ProximityPrize.SubmissionLower.RCN247
end PackedLegacy_FW

/-! Packed from ProximityPrize.SubmissionLower.O. -/
section PackedLegacy_O
namespace ProximityPrize.SubmissionLower.RCN111
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
noncomputable def indexedPlaneResidueWeight (a:A):ℕ:=by
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Fact (Irreducible q):=
   ⟨projectedFactor_irreducible Omega L order e (ht a) (hfinite a)⟩
 let a0:=residueAlgebra q J (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 exact Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J)
end
end ProximityPrize.SubmissionLower.RCN111
end PackedLegacy_O

/-! Packed from ProximityPrize.SubmissionLower.FY. -/
section PackedLegacy_FY
namespace ProximityPrize.SubmissionLower.RCN249
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN074 RCN245 RCN106 RCN111 RCN095 RCN120 RCN093 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN249.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN249.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) (A:Type) [Fintype A]
structure StageIndexedFlagFamily where
 component:A → StageComponent S
 injective:Function.Injective component
 lam:GenericField K
 mu:GenericField K
 nu:GenericField K
 order:Fin 3 ≃ Fin 3
 ht:∀ a,Transcendental (GenericField K)
   (flagEvaluation (GenericField K) (component a).1 lam mu nu
     (MvPolynomial.X (order 0)))
 finite:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   FiniteDimensional (RatFunc (GenericField K))
     (CoordinateField (GenericField K) (component a).1)
 generates:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   IntermediateField.adjoin (RatFunc (GenericField K))
     ({flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 2)),
       flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 1))}:
       Set (CoordinateField (GenericField K) (component a).1))=⊤
 positive:0 < (stageSurfacePlane S lam mu nu order).natDegree
structure StageIndexedFactor (F:StageIndexedFlagFamily S A) where
 q:Polynomial (RatFunc (GenericField K))
 irreducible:Irreducible q
 monic:q.Monic
 witness:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def stageFamilyGroupedExponent
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):ℕ:=
 ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
   localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
     indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
       F.ht F.finite a.1
@[simp] theorem stageFamilyGroupedExponent_eq
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (q):
   stageFamilyGroupedExponent S A hfirstProper F q=
     ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
         indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
           F.ht F.finite a.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN249
end PackedLegacy_FY

/-! Packed from ProximityPrize.SubmissionLower.J9. -/
section PackedLegacy_J9
namespace ProximityPrize.SubmissionLower.RCN102
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN226 RCN191 RCN120 RCN113 RCN225 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_J9

/-! Packed from ProximityPrize.SubmissionLower.C5. -/
section PackedLegacy_C5
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem transformedSurface_irreducible
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   Irreducible (planeMap Omega order (flagAlgHom lam mu nu G)):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 exact planeMap_irreducible_of_evaluation Omega (CoordinateField Omega C.1)
   order e (flagAlgHom lam mu nu G)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC
theorem transformedSurface_not_dvd_tail
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   ¬ planeMap Omega order (flagAlgHom lam mu nu G)∣
     planeMap Omega order (flagAlgHom lam mu nu T):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 intro hdiv
 have hflagDvd:=(planeMap_dvd_iff_of_evaluation Omega
   (CoordinateField Omega C.1) order e
     (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC).mp hdiv
 exact hproper ((flag_dvd_iff lam mu nu G T).mp hflagDvd)
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_C5

/-! Packed from ProximityPrize.SubmissionLower.K0. -/
section PackedLegacy_K0
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_K0

/-! Packed from ProximityPrize.SubmissionLower.K3. -/
section PackedLegacy_K3
namespace ProximityPrize.SubmissionLower.RCN108
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN103 RCN106 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
theorem indexed_denominators_disjoint_surface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint (((Ideal.span {q}).primeCompl.map
     (Polynomial.C:Polynomial (RatFunc Omega) →+*PlaneRing Omega).toMonoidHom):
     Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hsurface:planeMap Omega order (flagAlgHom lam mu nu G)∈J:=by
   change planeEvaluation Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (planeMap Omega order (flagAlgHom lam mu nu G))=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   change flagEvaluation Omega (component a.1).1 lam mu nu
     (flagAlgHom lam mu nu G)=0
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega (component a.1).1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H (component a.1)
 rw [Set.disjoint_left]
 intro x hx hxSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp hxSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem indexedFiberSurface_span_isPrime
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (Ideal.span {fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (transformedSurface_irreducible lam mu nu order hG
       (component a.1) (ht a.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)})
     hglobal (indexed_denominators_disjoint_surface
       component lam mu nu order ht q hq a)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem indexedFiberTail_not_mem_surface
   (hG:Irreducible G) (hproper:¬ G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom lam mu nu T))∉
     Ideal.span {fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega →+*Polynomial R:=fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (transformedSurface_irreducible lam mu nu order hG
         (component a.1) (ht a.1)).prime)
     (indexed_denominators_disjoint_surface component lam mu nu order ht q hq a)
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   simpa only [Ideal.map_span,Set.image_singleton] using hmem
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact transformedSurface_not_dvd_tail lam mu nu order hG hproper
   (component a.1) (ht a.1) (Ideal.mem_span_singleton.mp hglobal)
end
end ProximityPrize.SubmissionLower.RCN108
end PackedLegacy_K3

/-! Packed from ProximityPrize.SubmissionLower.FK. -/
section PackedLegacy_FK
namespace ProximityPrize.SubmissionLower.RCN227
open UniqueFactorizationMonoid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [DecidableEq K]
theorem ord_algebraMap_eq_normalizedFactors_count
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic)
   (hr:r≠0):
   Ring.ord (Localization.AtPrime p)
     (algebraMap (Polynomial K) (Localization.AtPrime p) r)=
       ((normalizedFactors r).count q:ℕ∞):=by
 let R:=Localization.AtPrime p
 have hp0:p≠⊥:=by
   rw [hp,ne_eq,Ideal.span_singleton_eq_bot]
   exact hq.ne_zero
 letI:IsDiscreteValuationRing R:=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial K) hp0 R
 have hem:emultiplicity q r=((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 have hfinite:FiniteMultiplicity q r:=
   finiteMultiplicity_of_emultiplicity_eq_natCast hem
 let e:ℕ:=(normalizedFactors r).count q
 have hmult:multiplicity q r=e:=by
   rw [multiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 obtain ⟨s,hrs,hqNotDvd⟩:=hfinite.exists_eq_pow_mul_and_not_dvd
 rw [hmult] at hrs
 have hsNotMem:s∉p:=by
   simpa only [hp,Ideal.mem_span_singleton] using hqNotDvd
 have hsUnit:IsUnit (algebraMap (Polynomial K) R s):=
   (IsLocalization.AtPrime.isUnit_to_map_iff R p s).mpr hsNotMem
 have hqMapNe:algebraMap (Polynomial K) R q≠0:=
   by
     simpa only [map_zero] using
       (FaithfulSMul.algebraMap_injective (Polynomial K) R).ne hq.ne_zero
 have hmax:IsLocalRing.maximalIdeal R=
     Ideal.span {algebraMap (Polynomial K) R q}:=by
   calc
     IsLocalRing.maximalIdeal R=
         Ideal.map (algebraMap (Polynomial K) R) p:=by
       simpa only [R] using
         (Localization.AtPrime.map_eq_maximalIdeal (I:=p)).symm
     _=Ideal.map (algebraMap (Polynomial K) R) (Ideal.span {q}):=
       congrArg (Ideal.map (algebraMap (Polynomial K) R)) hp
     _=Ideal.span {algebraMap (Polynomial K) R q}:=by
       rw [Ideal.map_span]
       simp only [Set.image_singleton]
 have hqMapIrr:Irreducible (algebraMap (Polynomial K) R q):=
   IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
     _ hqMapNe hmax
 have hsNe:algebraMap (Polynomial K) R s≠0:=hsUnit.ne_zero
 have hrsMap:algebraMap (Polynomial K) R r=
     (algebraMap (Polynomial K) R q)^e*
       algebraMap (Polynomial K) R s:=by
   rw [hrs,map_mul,map_pow]
 change Ring.ord R (algebraMap (Polynomial K) R r)=_
 rw [hrsMap,
   Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hsNe),
   Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hqMapNe),
   Ring.ord_of_irreducible hqMapIrr,Ring.ord_of_isUnit hsUnit]
 simp [e]
theorem pow_sum_dvd_of_sum_le_localized_ord
   {I:Type*} [Fintype I]
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic) (hr:r≠0)
   (multiplicity:I → ℕ)
   (hle:((∑ i,multiplicity i:ℕ):ℕ∞) ≤
     Ring.ord (Localization.AtPrime p)
       (algebraMap (Polynomial K) (Localization.AtPrime p) r)):
   q^(∑ i,multiplicity i)∣r:=by
 rw [ord_algebraMap_eq_normalizedFactors_count p q r hp hq hqMonic hr] at hle
 have hcount:(∑ i,multiplicity i) ≤ (normalizedFactors r).count q:=by
   exact_mod_cast hle
 have hem:emultiplicity q r=
     ((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 apply pow_dvd_of_le_emultiplicity
 rw [hem]
 exact_mod_cast hcount
end
end ProximityPrize.SubmissionLower.RCN227
end PackedLegacy_FK

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier22 : True := by trivial
end ProximityPrize.SubmissionLower
end Compact_PackedLegacy


