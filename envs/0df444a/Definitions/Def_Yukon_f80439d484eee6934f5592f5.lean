-- Prove2me | Definitions.Def_Yukon_f80439d484eee6934f5592f5
-- name    : Yukon_f80439d484eee6934f5592f5
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T02:58:38.426828+00:00
-- url     : https://prove2.me/theorems/a4f36bbd-2cee-4031-a6cb-13c3b6d92a27
-- title:
--   LowerFoundation source section 8
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-direct-dependency-Yukon_f80439d484eee6934f5592f5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNDkyNjBhNTlhNWEwNDBhM2VhOGI3Njk2M2MwZTkzOTNiYTUyMzNiMWJhMWYyODJlYmY1ZmU5MjM2ZWM3Y2VlNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fZjgwNDM5ZDQ4NGVlZTY5MzRmNTU5MmY1IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZjgwNDM5ZDQ4NGVlZTY5MzRmNTU5MmY1IiwidiI6Mn0]

import Definitions.Def_Yukon_4170405954707ce09a9eb539
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.FF. -/
section PackedLegacy_FF
namespace ProximityPrize.SubmissionLower.RCN218
open RCN313 RCN077 RCN136 RCN055 RCN188 RCN270 RCN186 RCN230 IsLocalRing
variable {K:Type*} [Field K]
abbrev Poly:=MvPolynomial (Fin 4) K
noncomputable def factorIdeal (F:Poly (K:=K)):Ideal (Poly (K:=K)):=Ideal.span {F}
theorem factorIdeal_isPrime (F:Poly (K:=K)) (hF:Irreducible F):
   (factorIdeal F).IsPrime:=by
 exact (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
noncomputable def contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)):
   Ideal (Poly (K:=K)):=
 C.comap (surfaceMap phi)
instance contractedPrime_isPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)) [C.IsPrime]:
   (contractedPrime phi C).IsPrime:=by
 exact Ideal.comap_isPrime (surfaceMap phi) C
theorem mem_contractedPrime_iff {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (A:Poly (K:=K)):
   A∈contractedPrime phi C ↔ surfaceMap phi A∈C:=
 Iff.rfl
theorem factorIdeal_le_contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (F:Poly (K:=K)) (hF:surfaceMap phi F∈C):
   factorIdeal F ≤ contractedPrime phi C:=by
 apply Ideal.span_le.2
 intro A hA
 simpa only [Set.mem_singleton_iff] using hA ▸ hF
noncomputable abbrev FactorLocal
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   (hFp:factorIdeal F ≤ p):Type _:=
 LocalizedQuotient (factorIdeal F) p hFp
theorem derivation_mem_maximal_of_mem_sq
   {A:Type*} [CommRing A] [Algebra K A] [IsLocalRing A]
   (D:Derivation K A A) (x:A) (hx:x∈maximalIdeal A^2):
   D x∈maximalIdeal A:=by
 rw [pow_two] at hx
 refine Submodule.mul_induction_on hx ?_ ?_
 · intro a ha b hb
   rw [D.leibniz]
   simpa [Algebra.smul_def] using (maximalIdeal A).add_mem
     ((maximalIdeal A).mul_mem_right (D b) ha)
     ((maximalIdeal A).mul_mem_right (D a) hb)
 · intro a b ha hb
   simpa only [map_add] using (maximalIdeal A).add_mem ha hb
noncomputable def factorAmbientQuotientEquiv
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   (Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}) ≃+*
     FactorLocal F p hFp:=
 (Ideal.quotEquivOfEq (by
   simp only [factorIdeal,Ideal.map_span,Set.image_singleton])).trans
   (quotientAmbientEquivLocalizedQuotient (factorIdeal F) p hFp)
theorem factorLocal_isRegularLocalRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p)
   (hdimFactor:ringKrullDim (FactorLocal F p hFp)=1):
   IsRegularLocalRing (FactorLocal F p hFp):=by
 letI:IsRegularLocalRing (Localization.AtPrime p):=
   mvPolynomial_atPrime_isRegularLocalRing p
 let A:=Localization.AtPrime p
 let f:A:=algebraMap (Poly (K:=K)) A F
 have hdim:ringKrullDim A=2:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A,hheight]
   norm_num
 have hf:f∈maximalIdeal A:=by
   exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p F).mpr
     (hFp (Ideal.mem_span_singleton_self F))
 have hf2:f∉maximalIdeal A^2:=by
   intro hf2
   let D:Derivation K A A:=localizationDerivation p.primeCompl
     (MvPolynomial.pderiv (2:Fin 4):Derivation K (Poly (K:=K)) _)
   have hDmem:D f∈maximalIdeal A:=derivation_mem_maximal_of_mem_sq D f hf2
   have hD:D f=algebraMap (Poly (K:=K)) A (polyH K F):=by
     exact localizationDerivation_algebraMap p.primeCompl _ F
   rw [hD] at hDmem
   exact hH ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p (polyH K F)).mp hDmem)
 haveI hsource:IsRegularLocalRing
     (Localization.AtPrime p ⧸ Ideal.span {
       algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}):=by
   change IsRegularLocalRing (A ⧸ Ideal.span {f})
   apply quotient_span_singleton_isRegularLocalRing f hf hf2 hdim
   calc
     ringKrullDim (A ⧸ Ideal.span {f})=
         ringKrullDim (FactorLocal F p hFp):=
       ringKrullDim_eq_of_ringEquiv (factorAmbientQuotientEquiv F p hFp)
     _=1:=hdimFactor
 exact IsRegularLocalRing.of_ringEquiv (R:=
   Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F})
   (factorAmbientQuotientEquiv F p hFp)
theorem quotientPrime_height_eq_one
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   (quotientPrime (factorIdeal F) p).height=1:=by
 let I:=factorIdeal F
 have hF0:F≠0:=by
   intro hzero
   subst F
   apply hH
   simp [polyH]
 have hFunit:¬ IsUnit F:=by
   intro hunit
   exact hfactorPrime.ne_top (by
     rw [factorIdeal,Ideal.span_singleton_eq_top]
     exact hunit)
 have hIheight:I.height=1:=by
   change (Ideal.span ({F}:Set (Poly (K:=K)))).height=1
   exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
     (by simpa [mem_nonZeroDivisors_iff_ne_zero] using hF0) hFunit
 have hIpne:I≠p:=by
   intro heq
   have:I.height=p.height:=congrArg Ideal.height heq
   rw [hIheight,hheight] at this
   norm_num at this
 have hIlt:I < p:=lt_of_le_of_ne hFp hIpne
 obtain ⟨x,hxp,hxI⟩:=SetLike.exists_of_lt hIlt
 have hmin:p∈(I ⊔ Ideal.span {x}).minimalPrimes:=by
   refine ⟨⟨inferInstance,sup_le hFp (Ideal.span_le.2 (by simpa))⟩,?_⟩
   intro r hr hrp
   rcases hr with ⟨hrprime,hJr⟩
   letI:r.IsPrime:=hrprime
   have hIr:I ≤ r:=le_sup_left.trans hJr
   have hIrne:I≠r:=by
     intro heq
     apply hxI
     rw [heq]
     exact hJr ((show Ideal.span {x} ≤ I ⊔ Ideal.span {x} from le_sup_right)
       (Ideal.mem_span_singleton_self x))
   have hIrlt:I < r:=lt_of_le_of_ne hIr hIrne
   have hrpEq:r=p:=by
     apply le_antisymm hrp
     by_contra hnot
     have hrlt:r < p:=lt_of_le_of_ne hrp (Ne.symm (ne_of_not_le hnot))
     have h1:=Ideal.height_add_one_le_of_lt_of_isPrime hIrlt
     have h2:=Ideal.height_add_one_le_of_lt_of_isPrime hrlt
     have hbad:(3:ℕ∞) ≤ p.height:=by
       calc
         3=I.height+1+1:=by rw [hIheight];norm_num
         _ ≤ r.height+1:=by
           simpa [add_comm,add_left_comm,add_assoc] using add_le_add_left h1 1
         _ ≤ p.height:=h2
     rw [hheight] at hbad
     norm_num at hbad
   exact hrpEq.ge
 apply le_antisymm
 · exact Ideal.map_height_le_one_of_mem_minimalPrimes hmin
 · rw [Order.one_le_iff_ne_zero]
   intro hz
   have hqbot:quotientPrime I p=⊥:=Ideal.height_eq_zero_iff_eq_bot.mp hz
   have hcomap:=quotientPrime_comap_quotientMk I p hFp
   rw [hqbot] at hcomap
   have hpI:p=I:=by
     change RingHom.ker (Ideal.Quotient.mk I)=p at hcomap
     rw [Ideal.mk_ker] at hcomap
     exact hcomap.symm
   exact hIpne hpI.symm
theorem factorLocal_isDiscreteValuationRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   IsDiscreteValuationRing (FactorLocal F p hFp):=by
 have hdim:ringKrullDim (FactorLocal F p hFp)=1:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height
     (quotientPrime (factorIdeal F) p) (FactorLocal F p hFp)]
   exact_mod_cast quotientPrime_height_eq_one F p hFp hheight hH
 letI:IsRegularLocalRing (FactorLocal F p hFp):=
   factorLocal_isRegularLocalRing F p hFp hheight hH hdim
 exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim
public theorem baseDerivation_self (F:Poly (K:=K)):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
public theorem baseDerivation_stable_factor (F:Poly (K:=K)):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [factorIdeal,Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [(baseDerivation F).leibniz,baseDerivation_self]
 simp
noncomputable def factorDerivation (F:Poly (K:=K)):
   Derivation K (Poly (K:=K) ⧸ factorIdeal F) (Poly (K:=K) ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F) (baseDerivation_stable_factor F)
noncomputable def factorLocalDerivation
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   Derivation K (FactorLocal F p hFp) (FactorLocal F p hFp):=
 localizationDerivation (K:=K)
   (R:=Poly (K:=K) ⧸ factorIdeal F) (S:=FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p).primeCompl (factorDerivation F)
theorem factorLocalDerivation_mk
   (F P:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   factorLocalDerivation F p hFp
       (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
         (Ideal.Quotient.mk (factorIdeal F) P))=
     algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
       (Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P)):=by
 rw [factorLocalDerivation,localizationDerivation_algebraMap]
 have hq:=RCN077.quotientDerivation_mk
   (K:=K) (A:=Poly (K:=K)) (baseDerivation F) (factorIdeal F)
     (baseDerivation_stable_factor F) P
 exact congrArg
   (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp))
   (by simpa only [factorDerivation] using hq)
noncomputable def factorLocalImage
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (P:Poly (K:=K)):FactorLocal F p hFp:=
 algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
   (Ideal.Quotient.mk (factorIdeal F) P)
theorem factorLocal_numerator_succ
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (b:ℕ):
   factorLocalImage F p hFp (numerator K F (b+1))=
     factorLocalImage F p hFp (polyH K F)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (numerator K F b))-
       (2*b:FactorLocal F p hFp)*
         factorLocalImage F p hFp (numerator K F b)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (polyH K F)):=by
 rw [numerator_succ,numeratorStep_eq]
 simp only [factorLocalImage,map_sub,map_mul,map_natCast]
 rw [←factorLocalDerivation_mk F (numerator K F b) p hFp,
   ←factorLocalDerivation_mk F (polyH K F) p hFp]
 push_cast
 ring
theorem factorLocal_image_isUnit_of_not_mem
   (F A:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hA:A∉p):
   IsUnit (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
     (Ideal.Quotient.mk (factorIdeal F) A)):=by
 apply (IsLocalization.AtPrime.isUnit_to_map_iff (FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p) _).mpr
 intro hmem
 apply hA
 have hmem':A∈(quotientPrime (factorIdeal F) p).comap
     (Ideal.Quotient.mk (factorIdeal F)):=hmem
 rw [quotientPrime_comap_quotientMk (factorIdeal F) p hFp] at hmem'
 exact hmem'
end ProximityPrize.SubmissionLower.RCN218
end PackedLegacy_FF

/-! Packed from ProximityPrize.SubmissionLower.CJ. -/
section PackedLegacy_CJ
namespace ProximityPrize.SubmissionLower.RCN326
open ProximityPrize.Benchmark RCN095 RCN100 RCN119
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def w:ℕ:=131071
namespace Profile
end Profile
end
end ProximityPrize.SubmissionLower.RCN326
end PackedLegacy_CJ

/-! Packed from ProximityPrize.SubmissionLower.Q7. -/
section PackedLegacy_Q7
namespace ProximityPrize.SubmissionLower.RCN339
open RCN095 RCN237 RCN264 RCN326
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1:FlagDegree}
theorem yzCost_mul_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ B.weightedCost r C:=by
 unfold PrimeFlagBudgetFamily.weightedCost
 calc
   coefficient*B.yzCost C ≤ r.yz*B.yzCost C:=
     Nat.mul_le_mul_right (B.yzCost C) hcoefficient
   _ ≤ r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C:=by
     omega
end
end ProximityPrize.SubmissionLower.RCN339
end PackedLegacy_Q7

/-! Packed from ProximityPrize.SubmissionLower.FE. -/
section PackedLegacy_FE
namespace ProximityPrize.SubmissionLower.RCN217
open RCN077 RCN313
 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
public abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
public theorem baseDerivation_self (F:Poly4 K):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
public theorem baseDerivation_stable_factor (F:Poly4 K):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [leibniz_product,baseDerivation_self]
 ring
public def factorDerivation (F:Poly4 K):
   Derivation K (Poly4 K ⧸ factorIdeal F) (Poly4 K ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F)
   (baseDerivation_stable_factor F)
public theorem factorDerivation_mk (F P:Poly4 K):
   factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P)=
     Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P):=
 quotientDerivation_mk _ _ _ P
public theorem factor_zero (F:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) F=0:=
 Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
public theorem polyH_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul,factor_zero]
 ring
public theorem polyG_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyG K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyG K F):=by
 unfold polyG
 simp only [MvPolynomial.pderiv_mul,map_neg,map_add,map_mul,factor_zero]
 ring
public theorem baseDerivation_mul_factor_mod (F Q P:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (baseDerivation (F*Q) P)=
     Ideal.Quotient.mk (factorIdeal F) Q*
       factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P):=by
 rw [factorDerivation_mk,baseDerivation_apply,baseDerivation_apply]
 simp only [map_add,map_mul]
 rw [polyH_mul_factor_mod,polyG_mul_factor_mod]
 ring
public theorem scaled_step_identity {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (q h n nS:A) (b:ℕ)
   (hN:nS=q^(2*b)*n):
   q*h*(q*D nS)-(2*b:A)*nS*(q*D (q*h))=
     q^(2*(b+1))*(h*D n-(2*b:A)*n*D h):=by
 cases b with
 | zero =>
     simp only [hN,mul_zero,pow_zero,one_mul,Nat.cast_zero,
       zero_mul,sub_zero]
     ring
 | succ c =>
     rw [hN]
     simp only [leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
       Nat.cast_mul,Nat.cast_ofNat]
     have he:2*(c+1)=2*c+2:=by omega
     have hesub:2*c+2-1=2*c+1:=by omega
     have henext:2*(c+1+1)=2*c+4:=by omega
     rw [he,hesub,henext]
     have hp1:q^(2*c+1)=q^(2*c)*q:=by
       rw [pow_add,pow_one]
     have hp2:q^(2*c+2)=q^(2*c)*q^2:=by rw [pow_add]
     have hp4:q^(2*c+4)=q^(2*c)*q^4:=by rw [pow_add]
     rw [hp1,hp2,hp4]
     ring
public theorem numerator_scaling_mod (F Q:Poly4 K) (b:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*b)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F b):=by
 induction b with
 | zero => simp
 | succ b ih =>
   change Ideal.Quotient.mk (factorIdeal F)
       (numeratorStep K (F*Q) b (numerator K (F*Q) b))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*(b+1))*
       Ideal.Quotient.mk (factorIdeal F)
         (numeratorStep K F b (numerator K F b))
   rw [numeratorStep_eq,numeratorStep_eq]
   simp only [map_sub,map_mul,map_natCast]
   rw [polyH_mul_factor_mod,
     baseDerivation_mul_factor_mod F Q (numerator K (F*Q) b),
     baseDerivation_mul_factor_mod F Q (polyH K (F*Q))]
   rw [←factorDerivation_mk F (numerator K F b),
     ←factorDerivation_mk F (polyH K F)]
   have hDH:=congrArg (factorDerivation F) (polyH_mul_factor_mod F Q)
   rw [hDH]
   simp only [Nat.cast_mul,Nat.cast_ofNat]
   apply scaled_step_identity (factorDerivation F)
     (Ideal.Quotient.mk (factorIdeal F) Q)
     (Ideal.Quotient.mk (factorIdeal F) (polyH K F))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K F b))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b))
     b
   exact ih
theorem numerator_sub_factor_power_mem (F Q:Poly4 K) (b:ℕ):
   numerator K (F*Q) b-Q^(2*b)*numerator K F b∈
     Ideal.span ({F}:Set (Poly4 K)):=by
 rw [←Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 simpa only [map_mul,map_pow] using numerator_scaling_mod F Q b
theorem factor_dvd_numerator_sub_power (F Q:Poly4 K) (b:ℕ):
   F∣numerator K (F*Q) b-Q^(2*b)*numerator K F b:=by
 exact Ideal.mem_span_singleton.mp (numerator_sub_factor_power_mem F Q b)
theorem factor_dvd_numerator_sub_power_of_eq (F Q S:Poly4 K)
   (hS:S=F*Q) (b:ℕ):
   F∣numerator K S b-Q^(2*b)*numerator K F b:=by
 subst S
 exact factor_dvd_numerator_sub_power F Q b
end
end ProximityPrize.SubmissionLower.RCN217
end PackedLegacy_FE
end Compact_PackedLegacy


