-- Prove2me | Definitions.Def_Yukon_28e0be7dc74857fb9ba06094
-- name    : Yukon_28e0be7dc74857fb9ba06094
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T02:35:23.702993+00:00
-- url     : https://prove2.me/theorems/0ff8ef31-0f15-4aea-a926-29648147c205
-- title:
--   LowerFoundation source section 6
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-direct-dependency-Yukon_28e0be7dc74857fb9ba06094
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMWQ2M2UxMjI5YzQ4MmE4NWRlZGM3ZmFjYWE4MTViNjVkZWFiOTIwNjBjYzhjNGY0M2YxZTNmODg5YTNmNjc2ZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fMjhlMGJlN2RjNzQ4NTdmYjliYTA2MDk0IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMjhlMGJlN2RjNzQ4NTdmYjliYTA2MDk0IiwidiI6Mn0]

import Definitions.Def_Yukon_89a5b4e3fafc2c387ec2fee8
import Definitions.Def_Yukon_0c4b393a1b9d5d6abf9784b7
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.O2. -/
section PackedLegacy_O2
namespace ProximityPrize.SubmissionLower.RCN270
open IsLocalRing Ideal
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {A:Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
public theorem exists_pair_generator_of_not_mem_sq
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2):
   ∃ g∈maximalIdeal A,maximalIdeal A=Ideal.span {f,g}:=by
 classical
 let m:=maximalIdeal A
 have hfg:m.FG:=m.fg_of_isNoetherianRing
 have hrank:m.spanFinrank=2:=by
   have hreg:=(isRegularLocalRing_iff A).mp (inferInstance:IsRegularLocalRing A)
   rw [hdim] at hreg
   exact_mod_cast hreg
 have hcard:m.generators.ncard=2:=by
   rw [Submodule.FG.generators_ncard hfg,hrank]
 obtain ⟨a,b,hab,hgen⟩:=Set.ncard_eq_two.mp hcard
 have hspan:Ideal.span {a,b}=m:=by
   simpa [hgen] using m.span_generators
 have ha:a∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hb:b∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hfm:f∈m:=by simpa [m] using hf
 have hfspan:f∈Ideal.span ({a,b}:Set A):=by rwa [hspan]
 obtain ⟨r,s,hrs⟩:=Ideal.mem_span_pair.mp hfspan
 have hunit:IsUnit r∨IsUnit s:=by
   letI:Decidable (IsUnit r):=Classical.propDecidable _
   letI:Decidable (IsUnit s):=Classical.propDecidable _
   by_cases hr:IsUnit r
   · exact Or.inl hr
   by_cases hs:IsUnit s
   · exact Or.inr hs
   · exfalso
     have hrm:r∈m:=(IsLocalRing.mem_maximalIdeal r).mpr hr
     have hsm:s∈m:=(IsLocalRing.mem_maximalIdeal s).mpr hs
     apply hf2
     rw [pow_two, ←hrs]
     exact (m*m).add_mem (Ideal.mul_mem_mul hrm ha) (Ideal.mul_mem_mul hsm hb)
 rcases hunit with hr | hs
 · refine ⟨b,hb,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,b}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       obtain ⟨u,rfl⟩:=hr
       have hfmem:f∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have hbmem:b∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have heq:a=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*s*b:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           a=((↑(u⁻¹):A)*(↑u:A))*a:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*((↑u:A)*a+s*b)-
               (↑(u⁻¹):A)*s*b:=by ring
       rw [heq]
       exact (Ideal.span ({f,b}:Set A)).sub_mem
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hbmem)
     · rw [hx]
       exact Ideal.subset_span (by simp)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
 · refine ⟨a,ha,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,a}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       exact Ideal.subset_span (by simp)
     · rw [hx]
       obtain ⟨u,rfl⟩:=hs
       have hfmem:f∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have hamem:a∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have heq:b=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*r*a:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           b=((↑(u⁻¹):A)*(↑u:A))*b:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*(r*a+(↑u:A)*b)-
               (↑(u⁻¹):A)*r*a:=by ring
       rw [heq]
       exact (Ideal.span ({f,a}:Set A)).sub_mem
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hamem)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
theorem quotient_span_singleton_isRegularLocalRing
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2)
   (hdimQ:ringKrullDim (A ⧸ Ideal.span {f})=1):
   IsRegularLocalRing (A ⧸ Ideal.span {f}):=by
 obtain ⟨g,hg,hmg⟩:=exists_pair_generator_of_not_mem_sq f hf hf2 hdim
 have hspanProper:Ideal.span ({f}:Set A)≠⊤:=by
   apply ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
   exact Ideal.span_le.2 (by simpa using hf)
 letI:Nontrivial (A ⧸ Ideal.span {f}):=
   Ideal.Quotient.nontrivial_iff.mpr hspanProper
 letI:IsLocalRing (A ⧸ Ideal.span {f}):=
   IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
     Ideal.Quotient.mk_surjective
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 rw [hdimQ]
 have hmax:maximalIdeal (A ⧸ Ideal.span {f})=
     Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:=by
   rw [←IsLocalRing.map_maximalIdeal_of_surjective
     (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,hmg,
     Ideal.map_span]
   simp [Set.image_insert_eq,Set.image_singleton]
 rw [hmax]
 have hle:(Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:
     Ideal (A ⧸ Ideal.span {f})).spanFinrank ≤ 1:=by
   exact (Submodule.spanFinrank_span_le_ncard_of_finite
     (Set.finite_singleton _)).trans (by simp)
 exact_mod_cast hle
end ProximityPrize.SubmissionLower.RCN270
end PackedLegacy_O2

/-! Packed from ProximityPrize.SubmissionLower.L5. -/
section PackedLegacy_L5
namespace ProximityPrize.SubmissionLower.RCN186
variable {A:Type*} [CommRing A]
noncomputable def quotientPrime (I p:Ideal A):Ideal (A ⧸ I):=
 p.map (Ideal.Quotient.mk I)
theorem quotientPrime_isPrime (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):(quotientPrime I p).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIp
noncomputable abbrev LocalizedQuotient (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):Type _:=
 @Localization.AtPrime (A ⧸ I) _ (quotientPrime I p)
   (quotientPrime_isPrime I p hIp)
theorem quotientPrime_comap_quotientMk (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):
   (quotientPrime I p).comap (Ideal.Quotient.mk I)=p:=by
 rw [quotientPrime,Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
 change p ⊔ RingHom.ker (Ideal.Quotient.mk I)=p
 rw [Ideal.mk_ker,sup_eq_left]
 exact hIp
theorem quotientMk_map_primeCompl (I p:Ideal A) [p.IsPrime]
   [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Submonoid.map (Ideal.Quotient.mk I) p.primeCompl=
     (quotientPrime I p).primeCompl:=by
 apply SetLike.ext
 intro x
 constructor
 · rintro ⟨s,hs,rfl⟩
   intro hmem
   exact hs ((quotientPrime_comap_quotientMk I p hIp).symm ▸ hmem)
 · intro hx
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective x
   refine ⟨s,?_,rfl⟩
   intro hs
   apply hx
   change s∈(quotientPrime I p).comap (Ideal.Quotient.mk I)
   rw [quotientPrime_comap_quotientMk I p hIp]
   exact hs
noncomputable def ambientToLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Localization.AtPrime p →+*LocalizedQuotient I p hIp:=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 exact IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
   p.primeCompl.le_comap_map
theorem ambientToLocalizedQuotient_surjective
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Function.Surjective (ambientToLocalizedQuotient I p hIp):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 simpa only [ambientToLocalizedQuotient] using
   (IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
     (LocalizedQuotient I p hIp) Ideal.Quotient.mk_surjective)
theorem ambientToLocalizedQuotient_ker
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   RingHom.ker (ambientToLocalizedQuotient I p hIp)=
     I.map (algebraMap A (Localization.AtPrime p)):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 have hk:=IsLocalization.ker_map (S:=Localization.AtPrime p)
   (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I) hM
 let canonicalMap:Localization.AtPrime p →+*LocalizedQuotient I p hIp:=
   IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
     (hM.symm ▸ p.primeCompl.le_comap_map)
 have hmaps:ambientToLocalizedQuotient I p hIp=canonicalMap:=by
   apply IsLocalization.ringHom_ext p.primeCompl
   simp only [ambientToLocalizedQuotient,canonicalMap,IsLocalization.map_comp]
 rw [hmaps]
 change RingHom.ker canonicalMap=_
 calc
   RingHom.ker canonicalMap=RingHom.ker
       (IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
         (hM.symm ▸ p.primeCompl.le_comap_map)):=by
     congr 1
   _=I.map (algebraMap A (Localization.AtPrime p)):=by
     simpa only [Ideal.mk_ker] using hk
noncomputable def quotientAmbientEquivLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) ≃+*
     LocalizedQuotient I p hIp:=
 (Ideal.quotEquivOfEq (ambientToLocalizedQuotient_ker I p hIp).symm).trans
   (RingHom.quotientKerEquivOfSurjective
     (ambientToLocalizedQuotient_surjective I p hIp))
end ProximityPrize.SubmissionLower.RCN186
end PackedLegacy_L5

/-! Packed from ProximityPrize.SubmissionLower.I8. -/
section PackedLegacy_I8
namespace ProximityPrize.SubmissionLower.RCN078
def DualNumber (R:Type*):=R × R
namespace DualNumber
variable {K R:Type*}
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instZero [Zero R]:Zero (DualNumber R):=inferInstanceAs (Zero (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instAdd [Add R]:Add (DualNumber R):=inferInstanceAs (Add (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instNeg [Neg R]:Neg (DualNumber R):=inferInstanceAs (Neg (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instSub [Sub R]:Sub (DualNumber R):=inferInstanceAs (Sub (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instAddCommMonoid [AddCommMonoid R]:AddCommMonoid (DualNumber R):=
 inferInstanceAs (AddCommMonoid (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instAddCommGroup [AddCommGroup R]:AddCommGroup (DualNumber R):=
 inferInstanceAs (AddCommGroup (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instSMul [SMul K R]:SMul K (DualNumber R):=inferInstanceAs (SMul K (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instIsScalarTower {L:Type*} [SMul L K] [SMul L R] [SMul K R] [IsScalarTower L K R]:
   IsScalarTower L K (DualNumber R):=
 inferInstanceAs (IsScalarTower L K (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instModule [Semiring K] [AddCommMonoid R] [Module K R]:Module K (DualNumber R):=
 inferInstanceAs (Module K (R × R))
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instOneOfZero [One R] [Zero R]:One (DualNumber R):=⟨(1,0)⟩
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instMulOfAdd [Mul R] [Add R]:Mul (DualNumber R):=
 ⟨fun x y => (x.1*y.1,x.1*y.2+x.2*y.1)⟩
@[ext]
theorem ext {x y:DualNumber R} (h₁:x.1=y.1) (h₂:x.2=y.2):x=y:=
 Prod.ext h₁ h₂
@[simp] theorem fst_zero [Zero R]:(0:DualNumber R).1=0:=rfl
@[simp] theorem snd_zero [Zero R]:(0:DualNumber R).2=0:=rfl
@[simp] theorem fst_add [Add R] (x y:DualNumber R):(x+y).1=x.1+y.1:=rfl
@[simp] theorem snd_add [Add R] (x y:DualNumber R):(x+y).2=x.2+y.2:=rfl
@[simp] theorem fst_one [One R] [Zero R]:(1:DualNumber R).1=1:=rfl
@[simp] theorem snd_one [One R] [Zero R]:(1:DualNumber R).2=0:=rfl
@[simp] theorem fst_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).1=x.1*y.1:=rfl
@[simp] theorem snd_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).2=x.1*y.2+x.2*y.1:=rfl
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instCommRing [CommRing R]:CommRing (DualNumber R) where
 mul_assoc x y z:=by ext <;> simp [mul_assoc,mul_add,add_mul];ring
 one_mul x:=by ext <;> simp
 mul_one x:=by ext <;> simp
 left_distrib x y z:=by ext <;> simp [mul_add];ring
 right_distrib x y z:=by ext <;> simp [add_mul];ring
 zero_mul x:=by ext <;> simp
 mul_zero x:=by ext <;> simp
 mul_comm x y:=by ext <;> simp [mul_comm,add_comm]
def inlRingHom [CommRing R]:R →+*DualNumber R where
 toFun r:=(r,0)
 map_one':=rfl
 map_mul' _ _:=by ext <;> simp
 map_zero':=rfl
 map_add' _ _:=by ext <;> simp
instance  _root_.ProximityPrize.SubmissionLower.RCN078.DualNumber.instAlgebra [CommRing K] [CommRing R] [Algebra K R]:Algebra K (DualNumber R) where
 algebraMap:=inlRingHom.comp (algebraMap K R)
 commutes' k x:=by ext <;> simp [mul_comm]
 smul_def' k x:=by
   apply Prod.ext
   · change k • x.1=algebraMap K R k*x.1
     exact Algebra.smul_def k x.1
   · change k • x.2=algebraMap K R k*x.2+0*x.1
     simp [Algebra.smul_def]
@[simp]
theorem algebraMap_apply [CommRing K] [CommRing R] [Algebra K R] (k:K):
   algebraMap K (DualNumber R) k=(algebraMap K R k,0):=rfl
def fstHom [CommRing K] [CommRing R] [Algebra K R]:DualNumber R →ₐ[K] R where
 toFun x:=x.1
 map_one':=rfl
 map_mul' _ _:=rfl
 map_zero':=rfl
 map_add' _ _:=rfl
 commutes' _:=rfl
def sndHom [CommRing R]:DualNumber R →ₗ[R] R where
 toFun x:=x.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
theorem isUnit_of_isUnit_fst [CommRing R] {x:DualNumber R} (hx:IsUnit x.1):
   IsUnit x:=by
 rcases x with ⟨a,b⟩
 rcases hx with ⟨u,hu⟩
 change (u:R)=a at hu
 subst a
 refine ⟨{
   val:=((u:R),b)
   inv:=((↑u⁻¹:R), -((↑u⁻¹:R)*b*(↑u⁻¹:R)))
   val_inv:=?_
   inv_val:=?_},rfl⟩
 · ext <;> simp [mul_assoc]
 · ext <;> simp [mul_assoc]
end DualNumber
end ProximityPrize.SubmissionLower.RCN078
end PackedLegacy_I8

/-! Packed from ProximityPrize.SubmissionLower.L6. -/
section PackedLegacy_L6
namespace ProximityPrize.SubmissionLower.RCN188
open RCN078
variable {K R S:Type*} [CommRing K] [CommRing R] [CommRing S]
 [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
 (M:Submonoid R) [IsLocalization M S]
def derivationDualAlgHom (D:Derivation K R R):R →ₐ[K] DualNumber S where
 toFun r:=(algebraMap R S r,algebraMap R S (D r))
 map_one':=by
   apply DualNumber.ext <;> simp
 map_mul' x y:=by
   apply DualNumber.ext
   · simp
   · simp [D.leibniz]
     exact mul_comm _ _
 map_zero':=by
   apply DualNumber.ext <;> simp
 map_add' x y:=by
   apply DualNumber.ext <;> simp
 commutes' k:=by
   apply DualNumber.ext
   · exact (IsScalarTower.algebraMap_apply K R S k).symm
   · simp
theorem derivationDualAlgHom_isUnit (D:Derivation K R R) (y:M):
   IsUnit (derivationDualAlgHom (S:=S) D y):=by
 apply DualNumber.isUnit_of_isUnit_fst
 simpa [derivationDualAlgHom] using IsLocalization.map_units S y
noncomputable def localizedDualAlgHom (D:Derivation K R R):
   S →ₐ[K] DualNumber S:=
 IsLocalization.liftAlgHom (derivationDualAlgHom_isUnit M D)
@[simp]
theorem localizedDualAlgHom_algebraMap (D:Derivation K R R) (r:R):
   localizedDualAlgHom M D (algebraMap R S r)=
     (algebraMap R S r,algebraMap R S (D r)):=by
 simp [localizedDualAlgHom,derivationDualAlgHom]
theorem localizedDualAlgHom_fst (D:Derivation K R R) (x:S):
   (localizedDualAlgHom M D x).fst=x:=by
 have hhom:
     (DualNumber.fstHom (K:=K) (R:=S)).comp
       (localizedDualAlgHom M D)=AlgHom.id K S:=by
   have hr:
       ((DualNumber.fstHom (K:=K) (R:=S)).comp
         (localizedDualAlgHom M D)).toRingHom=
         (AlgHom.id K S).toRingHom:=by
     apply IsLocalization.ringHom_ext M
     ext r
     simp [DualNumber.fstHom]
   exact AlgHom.ext fun x => RingHom.congr_fun hr x
 exact AlgHom.congr_fun hhom x
noncomputable def localizationDerivation (D:Derivation K R R):Derivation K S S:=
 Derivation.mk'
   ((DualNumber.sndHom (R:=S)).restrictScalars K |>.comp
     (localizedDualAlgHom M D).toLinearMap)
   (by
     intro x y
     change (localizedDualAlgHom M D (x*y)).snd=
       x*(localizedDualAlgHom M D y).snd+
         y*(localizedDualAlgHom M D x).snd
     rw [map_mul,DualNumber.snd_mul,
       localizedDualAlgHom_fst M D x,localizedDualAlgHom_fst M D y]
     simp
     ring)
@[simp]
theorem localizationDerivation_algebraMap (D:Derivation K R R) (r:R):
   localizationDerivation M D (algebraMap R S r)=algebraMap R S (D r):=by
 change (localizedDualAlgHom M D (algebraMap R S r)).snd=_
 rw [localizedDualAlgHom_algebraMap]
end ProximityPrize.SubmissionLower.RCN188
end PackedLegacy_L6
end Compact_PackedLegacy


