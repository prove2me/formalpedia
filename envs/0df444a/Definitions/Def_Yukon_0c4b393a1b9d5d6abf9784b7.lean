-- Prove2me | Definitions.Def_Yukon_0c4b393a1b9d5d6abf9784b7
-- name    : Yukon_0c4b393a1b9d5d6abf9784b7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T02:15:59.222864+00:00
-- url     : https://prove2.me/theorems/8c2c9634-fbc4-4878-8c78-81fe4bb8a82e
-- title:
--   LowerFoundation source module
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-i6-direct-dependency-Yukon_0c4b393a1b9d5d6abf9784b7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzUwYjU2NDVkZTgyOTY1NTdkYTNkOTRlZjJlMDExMGEzYzcwZjQzOThkZjU1YWM3OWQwM2FhNjhlZDJkMGE5NyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24taTYtZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fMGM0YjM5M2ExYjlkNWQ2YWJmOTc4NGI3IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMGM0YjM5M2ExYjlkNWQ2YWJmOTc4NGI3IiwidiI6Mn0]

import Definitions.Def_Yukon_126560b5c32e606e4eaf10e4


set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.I6. -/
section PackedLegacy_I6
namespace ProximityPrize.SubmissionLower.RCN073
open RCN324
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K R:Type} [Field K] [CommRing R] [IsDomain R]
 [Algebra K R] [IsDiscreteValuationRing R]
public theorem derivation_preserves_char_pow
   (D:Derivation K R R) (pi:R) (p:ℕ) [CharP R p]
   (_hp:1 ≤ p) (f:R) (hf:pi^p∣f):pi^p∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul,CharP.cast_eq_zero R p,zero_mul,
   mul_zero,add_zero]
 exact ⟨D u,rfl⟩
public theorem recurrence_preserves_dvd
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (a:R) (j:ℕ) (hN:a∣N j) (hDN:a∣D (N j)):
   a∣N (j+1):=by
 obtain ⟨u,hu⟩:=hN
 obtain ⟨v,hv⟩:=hDN
 refine ⟨H*v-c j*u*DH,?_⟩
 rw [hrec j,hv,hu]
 ring
public theorem tangent_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi a:R) (htangent:D pi=pi*a)
   (hN0:pi∣N 0):∀ j,pi∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec pi j ih
     simpa only [pow_one] using
       tangent_preserves_divisibility D pi a 1 (by simp) htangent
         (N j) (by simpa only [pow_one] using ih)
public theorem char_pow_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi:R) (p:ℕ) [CharP R p] (hp:1 ≤ p)
   (hN0:pi^p∣N 0):∀ j,pi^p∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec (pi^p) j ih
     exact derivation_preserves_char_pow D pi p hp (N j) ih
public theorem addVal_derivation_eq_pred
   (D:Derivation K R R) (pi:R) (hpi:Irreducible pi)
   (htrans:IsUnit (D pi)) (p k:ℕ) [CharP R p]
   (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (x:R) (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R (D x)=k-1:=by
 have h:=addVal_iterate_eq_sub_of_transverse D pi (u:R) k 1 p hp hkp
   hkpos hpi u.isUnit htrans
 rw [hx,mul_comm]
 simpa using h
public theorem transverse_recurrence_step
   (D:Derivation K R R) (H DH c x next pi:R)
   (hrec:next=H*D x-c*x*DH)
   (hH:IsUnit H) (hpi:Irreducible pi) (htrans:IsUnit (D pi))
   (p k:ℕ) [CharP R p] (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R next=k-1:=by
 let v:=IsDiscreteValuationRing.addVal R
 have hDx:v (D x)=k-1:=
   addVal_derivation_eq_pred D pi hpi htrans p k hp hkpos hkp x u hx
 have hxv:v x=k:=IsDiscreteValuationRing.addVal_def x u hpi k hx
 have hfirst:v (H*D x)=k-1:=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hH,zero_add,hDx]
 have hsecond:k ≤ v (c*x*DH):=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_mul,hxv]
   exact le_add_right (le_add_left (le_refl (k:ℕ∞)))
 have hlt:v (H*D x) < v (c*x*DH):=by
   rw [hfirst]
   exact (ENat.coe_lt_coe.mpr (Nat.pred_lt (Nat.ne_zero_of_lt hkpos))).trans_le hsecond
 rw [hrec,v.map_sub_eq_of_lt_left hlt,hfirst]
theorem recurrence_unit_or_persistent
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (p:ℕ) [CharP R p] (hp:p.Prime)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (hH:IsUnit H) (hN0ne:N 0≠0) (hN0nonunit:¬ IsUnit (N 0)):
   let mu:=(IsDiscreteValuationRing.addVal R (N 0)).toNat
   1 ≤ mu∧
     ((∃ delay,1 ≤ delay∧delay ≤ mu∧IsUnit (N delay))∨
       (∀ delay,¬ IsUnit (N delay))):=by
 classical
 let v:=IsDiscreteValuationRing.addVal R
 obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
 obtain ⟨mu,u,hN0⟩:=
   IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN0ne hpi
 have hv0:v (N 0)=mu:=IsDiscreteValuationRing.addVal_def (N 0) u hpi mu hN0
 have hmuDef:(v (N 0)).toNat=mu:=by rw [hv0];simp
 have hmuPos:1 ≤ mu:=by
   by_contra h
   have hz:mu=0:=Nat.eq_zero_of_not_pos h
   apply hN0nonunit
   apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
   change v (N 0)=0
   rw [hv0,hz]
   simp
 rw [hmuDef]
 refine ⟨hmuPos,?_⟩
 letI:Decidable (IsUnit (D pi)):=Classical.propDecidable _
 by_cases htrans:IsUnit (D pi)
 · by_cases hmup:mu < p
   · left
     refine ⟨mu,hmuPos,le_rfl,?_⟩
     have horders:∀ j ≤ mu,v (N j)=mu-j:=by
       intro j hj
       induction j with
       | zero => simpa using hv0
       | succ j ih =>
           have hjlt:j < mu:=by omega
           have hord:=ih hjlt.le
           have hNjNe:N j≠0:=by
             intro hz
             rw [hz,IsDiscreteValuationRing.addVal_zero] at hord
             exact ENat.top_ne_coe (mu-j) hord
           obtain ⟨k,uj,hNj⟩:=
             IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hNjNe hpi
           have hkv:v (N j)=k:=
             IsDiscreteValuationRing.addVal_def (N j) uj hpi k hNj
           have hk:k=mu-j:=by
             exact ENat.coe_inj.mp (hkv.symm.trans hord)
           have hkpos:1 ≤ k:=by omega
           have hkp:k < p:=by omega
           have hstep:=transverse_recurrence_step D H DH (c j) (N j)
             (N (j+1)) pi (hrec j) hH hpi htrans p k hp hkpos hkp uj hNj
           rw [hstep,hk]
           exact_mod_cast (show mu-j-1=mu-(j+1) by omega)
     exact IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by
       simpa using horders mu le_rfl)
   · right
     have hpLe:p ≤ mu:=Nat.le_of_not_gt hmup
     have hpPos:1 ≤ p:=hp.one_le
     have hpow:pi^p∣N 0:=by
       rw [hN0]
       refine ⟨(u:R)*pi^(mu-p),?_⟩
       have hpowEq:pi^mu=pi^p*pi^(mu-p):=by
         rw [←pow_add,Nat.add_sub_of_le hpLe]
       rw [hpowEq]
       ring
     have hall:=char_pow_chain D H DH c N hrec pi p hpPos hpow
     intro j hunit
     apply hpi.not_isUnit
     apply isUnit_of_dvd_one
     exact (dvd_pow_self pi (Nat.ne_of_gt hpPos)).trans
       ((hall j).trans (isUnit_iff_dvd_one.mp hunit))
 · right
   have hDmem:D pi∈IsLocalRing.maximalIdeal R:=
     (IsLocalRing.mem_maximalIdeal (D pi)).2 htrans
   obtain ⟨a,ha⟩:∃ a,D pi=pi*a:=by
     have hmax:=(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
     rw [hmax,Ideal.mem_span_singleton'] at hDmem
     obtain ⟨a,ha⟩:=hDmem
     exact ⟨a,by simpa [mul_comm] using ha.symm⟩
   have hpiDvd:pi∣N 0:=by
     rw [hN0]
     refine ⟨(u:R)*pi^(mu-1),?_⟩
     have hpowEq:pi^mu=pi*pi^(mu-1):=by
       calc
         pi^mu=pi^(1+(mu-1)):=by
           rw [Nat.add_sub_of_le hmuPos]
         _=pi^1*pi^(mu-1):=pow_add pi 1 (mu-1)
         _=pi*pi^(mu-1):=by rw [pow_one]
     rw [hpowEq]
     ring
   have hall:=tangent_chain D H DH c N hrec pi a ha hpiDvd
   intro j hunit
   exact hpi.not_isUnit (isUnit_of_dvd_one
     ((hall j).trans (isUnit_iff_dvd_one.mp hunit)))
end
end ProximityPrize.SubmissionLower.RCN073
end PackedLegacy_I6
end Compact_PackedLegacy


