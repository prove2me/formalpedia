-- Prove2me | Definitions.Def_Yukon_e30426b269ddc1b9e0d8c850
-- name    : Yukon_e30426b269ddc1b9e0d8c850
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T08:15:10.214467+00:00
-- url     : https://prove2.me/theorems/9e5cd42e-9761-4bc1-80f0-f11bba7f0516
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpacePowerSupplier6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-cb3c4a5342bd351cfdd5d752ddffe845192fe021e717d064fba26906dc77ab29
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjY3ZTEwNzcyZDJlMDhkMmE1MGQxMDFkYmUwNjE5YTQzYjU3MDA4MjI0YjU4NWY1ZDE4NDNlZjY1YjE0MzJkMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtY2IzYzRhNTM0MmJkMzUxY2ZkZDVkNzUyZGRmZmU4NDUxOTJmZTAyMWU3MTdkMDY0ZmJhMjY5MDZkYzc3YWIyOSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2UzMDQyNmIyNjlkZGMxYjllMGQ4Yzg1MCIsInYiOjJ9]

import Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0





















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Actual contact-source supply and the multiplicity-preserving coprime
cofactor handoff. The source nullity is discharged, not assumed. -/
namespace ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpaceSourceKernel6814
open WholeSpaceSourceCounts6814 SecondJetGlobalSupport

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

theorem contact_not_power_generic
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (hb : ∀ i, 2*e i 1+e i 3≤31) (hs : ∀ i, e i 1≤14)
    (hu : ∀ i, e i 1+e i 2+e i 3≤98)
    (ht : ∀ i, e i 1+e i 2+e i 3+e i 4≤1700)
    (hc : ∀ i, e i 0+131071*e i 2+131070*e i 3+131069*e i 1<cutoff (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 627003341034+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
        (fun h => (cutoff h+31-1)/131071)≤Fintype.card I)
    (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hgood : Good a) :
    ∃ P : Poly (K := K), P≠0 ∧ ¬J^a.q∣P ∧ Bounds P ∧
      ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes i) (u0 i) (u1 i) P) := by
  obtain ⟨V,hfinite,hdim,hsupport,hcontact⟩ := exists_contact_kernel e he
    72 1700 31 14 98 131071 cutoff (by omega) hb hs hu ht hc nodes u0 u1 627003341034 hcard
  letI : Module.Finite K V := hfinite
  have hbounds : ∀ P∈V, Bounds P := by
    intro P hP d hd
    obtain ⟨i,rfl⟩ := hsupport P hP d hd
    exact ⟨hb i,hs i,hu i,ht i,hc i⟩
  obtain ⟨P,hP,hnot⟩ := exists_not_dvd_power V hdim
    (fun P hP => (weights_of_bounds P (hbounds P hP)).1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.2.1)
    J hJ a ha hgood.1 hgood.2
  exact ⟨P,by intro hz; exact hnot (by rw [hz]; exact dvd_zero _),hnot,hbounds P hP,hcontact P hP⟩

theorem exists_interpolant_not_dvd_power (nodes : N ↪ K) (u0 u1 : N → K)
    (hN : Fintype.card N=262144) (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hgood : Good a) :
    ∃ P : Poly (K := K), P≠0 ∧ ¬J^a.q∣P ∧ Bounds P ∧
      ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes i) (u0 i) (u1 i) P) := by
  apply contact_not_power_generic
    (SecondJetRelaxedGlobalIndex.exponent (D := cutoff) (w := 131071) (L := 1700)
      (B := 31) (s := 14) (U := 98))
    (SecondJetRelaxedGlobalIndex.exponent_injective cutoff 131071 1700 31 14 98)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.2.2)
    nodes u0 u1 ?_ J hJ a ha hgood
  simpa only [hN] using source_nullity

theorem cofactor_of_not_power (J P : Poly (K := K)) (hJ : Irreducible J) (q : ℕ)
    (hnot : ¬J^q∣P) :
    ∃ e<q, ∃ Q : Poly (K := K), P=J^e*Q ∧ Q≠0 ∧ IsRelPrime J Q := by
  have hP : P≠0 := by intro hz; exact hnot (by rw [hz]; exact dvd_zero _)
  obtain ⟨e,Q,hnd,hEq⟩ := WfDvdMonoid.max_power_factor hP hJ
  have hQ : Q≠0 := by intro hz; apply hP; rw [hEq,hz,mul_zero]
  have he : e<q := by
    by_contra h
    exact hnot ((pow_dvd_pow J (by omega : q≤e)).trans ⟨Q,hEq⟩)
  exact ⟨e,he,Q,hEq,hQ,hJ.isRelPrime_iff_not_dvd.mpr hnd⟩

theorem residual_order_positive (m e : ℕ) (hm : 0<m)
    (he : e<MovingSourceNativeEnvelope6814.copies3 m) : 0<3-e*m := by
  by_cases hm1 : m=1
  · subst m; norm_num [MovingSourceNativeEnvelope6814.copies3] at he ⊢; omega
  by_cases hm2 : m=2
  · subst m; norm_num [MovingSourceNativeEnvelope6814.copies3] at he ⊢; omega
  have hq : MovingSourceNativeEnvelope6814.copies3 m=1 := by
    unfold MovingSourceNativeEnvelope6814.copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at he
  have he0 : e=0 := by omega
  simp [he0]

/-- Root order survives removal of every available J-power. The zero
specialization case is handled before using finite root multiplicity. -/
theorem cofactor_root_power {E : Type*} [Field E]
    (phi : Poly (K := K) →+* Polynomial E) (z : E)
    (J P Q : Poly (K := K)) (e m : ℕ) (hEq : P=J^e*Q)
    (hJ : phi J≠0) (hm : (phi J).rootMultiplicity z=m)
    (hp : (Polynomial.X-Polynomial.C z)^3∣phi P) :
    (Polynomial.X-Polynomial.C z)^(3-e*m)∣phi Q := by
  by_cases hQ : phi Q=0
  · rw [hQ]; exact dvd_zero _
  rw [hEq,map_mul,map_pow] at hp
  have hn := mul_ne_zero (pow_ne_zero e hJ) hQ
  have horder := (Polynomial.le_rootMultiplicity_iff hn).mpr hp
  rw [Polynomial.rootMultiplicity_mul hn,
    UniqueCurvatureOwner6814.rootMultiplicity_power (phi J) z e hJ,hm] at horder
  exact (Polynomial.le_rootMultiplicity_iff hQ).mp (by omega)







end
end ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814


