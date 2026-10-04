-- Prove2me | Definitions.Def_Yukon_8c903be4287ee925ec46b1a5
-- name    : Yukon_8c903be4287ee925ec46b1a5
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T08:14:32.973456+00:00
-- url     : https://prove2.me/theorems/53e410cb-a731-461a-958e-ce5d4fe3b6b7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceOwnerRouting6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-513ce97acf8df2f0e9a399e3024806e1c540e4c6328b7d6240094928aecbb02d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2JlZGQ2NTM3NTBhOWFlMWNiOWE2ZDg5NzVmZWVjZWUzMTkwNjk1ZmE5Y2IwYTZjOWI4NWZhOGYxZGQwMmZlMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNTEzY2U5N2FjZjhkZjJmMGU5YTM5OWUzMDI0ODA2ZTFjNTQwZTRjNjMyOGI3ZDYyNDAwOTQ5MjhhZWNiYjAyZCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzhjOTAzYmU0Mjg3ZWU5MjVlYzQ2YjFhNSIsInYiOjJ9]

import Definitions.Def_Yukon_8b73aecc71f3e1b6f34fc101




















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Actual two-source routing: a linear unique owner, a constructed
nonlinear native source with a checked-cell fitting price, or two coprime
owning factors. No unique-ownership premise is assumed by the split. -/
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingFiberThreeSources6811
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 MovingSourceTwoProfiles6814
open RCN234 RCN156

variable {K : Type} [Field K]

theorem source_caps (F : MvPolynomial (Fin 4) K) (S : Source F) :
    weightedTotalDegree slopeWeights S.P≤S.B ∧ weightedTotalDegree middleWeights S.P≤S.U ∧
      weightedTotalDegree totalWeights S.P≤S.T ∧ S.P.degreeOf 1≤S.s := by
  refine ⟨Finset.sup_le ?_,Finset.sup_le ?_,Finset.sup_le ?_,MvPolynomial.degreeOf_le_iff.mpr S.hS⟩
  · intro e he
    simpa [weight_coords,slopeWeights,Nat.mul_comm] using (S.hshape e he).1
  · intro e he
    simpa [weight_coords,middleWeights] using (S.hshape e he).2.1
  · intro e he
    simpa [weight_coords,totalWeights] using (S.hshape e he).2.2

public theorem two_caps (m e f a b c : ℕ) (hm : 0<m)
    (he : 3≤e*m) (hf : 7≤f*m) (ha : e*a≤b) (hb : f*a≤c) :
    a≤min (b/copies3 m) (c/copies7 m) := by
  apply le_min
  · apply (Nat.le_div_iff_mul_le (copies3_pos m hm)).mpr
    have hh := Nat.mul_le_mul_right a (copies3_le m e hm he)
    nlinarith
  · apply (Nat.le_div_iff_mul_le (copies7_pos m hm)).mpr
    have hh := Nat.mul_le_mul_right a (copies7_le m f hm hf)
    nlinarith

def NativeRoute (F : MvPolynomial (Fin 4) K) (J : WholeSpaceCube6814.Poly (K:=K)) : Prop :=
  ∃ m : ℕ, ∃ S : Source F, 0<m ∧ 2≤J.degreeOf 1 ∧ S.P=J ∧ S.d=m ∧
    S.flag=nativeFlag m (J.degreeOf 1) ∧
    scaledMain m (J.degreeOf 1)<3*272069082261391681*m

theorem unique_nonlinear_route [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S Sz : Source F) (hS : Profile S 31 98 995 14 2 3) (hZ : Profile Sz 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (huniqueS : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (huniqueZ : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J Sz.P)
    (hdegree : 2≤J.degreeOf 1) : NativeRoute F J := by
  rcases hS with ⟨hSB,hSU,hST,hSs,hSk,hSn⟩
  rcases hZ with ⟨hZB,hZU,hZT,hZs,hZk,hZn⟩
  let phi := carrierMap F
  let z := ratio phi F
  let m := (rootPolynomialMap phi J).rootMultiplicity z
  have hPs := canonical_source_power F S (by rw [hST]; omega) hpos hsmall (by rw [hSk]; omega)
  have hPz := canonical_source_power F Sz (by rw [hZT]; omega) hpos hsmall (by rw [hZk]; omega)
  have hs3 : (Polynomial.X-Polynomial.C z)^3 ∣ rootPolynomialMap phi S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣ (asS S.P).map (carrierMap F)
    simpa only [Source.d,hSk] using hPs.2
  have hz7 : (Polynomial.X-Polynomial.C z)^7 ∣ rootPolynomialMap phi Sz.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^7 ∣ (asS Sz.P).map (carrierMap F)
    simpa only [Source.d,hZk] using hPz.2
  have hJne : rootPolynomialMap phi J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap phi) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hPs.1 hd
  have hm : 0<m := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms : m≤J.degreeOf 1 := by
    have hh := Polynomial.natDegree_le_of_dvd
      ((rootPolynomialMap phi J).pow_rootMultiplicity_dvd z) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (asS_natDegree J))
  obtain ⟨e,he,heW,heS⟩ := unique_owner_charges phi z S.P J (source_nonzero F S) hJ huniqueS 3 m hJne rfl hs3
  obtain ⟨f,hf,hfW,hfS⟩ := unique_owner_charges phi z Sz.P J (source_nonzero F Sz) hJ huniqueZ 7 m hJne rfl hz7
  have hcS := source_caps F S
  have hcZ := source_caps F Sz
  rw [hSB,hSU,hST,hSs] at hcS
  rw [hZB,hZU,hZT,hZs] at hcZ
  have hcapB : weightedTotalDegree slopeWeights J≤capB m :=
    two_caps m e f _ 31 53 hm he hf ((heW slopeWeights).trans hcS.1) ((hfW slopeWeights).trans hcZ.1)
  have hcapU : weightedTotalDegree middleWeights J≤capU m :=
    two_caps m e f _ 98 177 hm he hf ((heW middleWeights).trans hcS.2.1) ((hfW middleWeights).trans hcZ.2.1)
  have hcapT : weightedTotalDegree totalWeights J≤capT m :=
    two_caps m e f _ 995 3429 hm he hf ((heW totalWeights).trans hcS.2.2.1) ((hfW totalWeights).trans hcZ.2.2.1)
  have hcapS : J.degreeOf 1≤capS m :=
    two_caps m e f _ 14 24 hm he hf (heS.trans hcS.2.2.2) (hfS.trans hcZ.2.2.2)
  have hshape : ∀ d ∈ J.support, 2*d 1+d 3≤capB m ∧
      d 1+d 2+d 3≤capU m ∧ d 1+d 2+d 3+d 4≤capT m := by
    intro d hd
    exact ⟨by simpa [weight_coords,slopeWeights,Nat.mul_comm] using
        (MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hcapB,
      by simpa [weight_coords,middleWeights] using
        (MvPolynomial.le_weightedTotalDegree middleWeights hd).trans hcapU,
      by simpa [weight_coords,totalWeights] using
        (MvPolynomial.le_weightedTotalDegree totalWeights hd).trans hcapT⟩
  have hhalf : J.degreeOf 1≤capB m/2 := MvPolynomial.degreeOf_le_iff.mpr (by
    intro d hd
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    have hh := (hshape d hd).1
    omega)
  have h2s : 2*J.degreeOf 1≤capB m := by
    have hh := Nat.mul_le_mul_right 2 hhalf
    have hd := Nat.div_mul_le_self (capB m) 2
    omega
  obtain ⟨R,hR,hRd,hRf⟩ := canonical_source_of_root J F hpos hsmall m (J.degreeOf 1)
    (capB m) (capU m) (capT m) hm rfl h2s (budget_caps m).1 (budget_caps m).2 hshape rfl
  exact ⟨m,R,hm,hdegree,hR,hRd,hRf,nonlinear_native_main_fits m _ hm hdegree hms hcapS h2s⟩

theorem retained_owner_routing [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S Sz : Source F) (hS : Profile S 31 98 995 14 2 3) (hZ : Profile Sz 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    ∃ J, Irreducible J ∧ J∣S.P ∧ rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0 ∧
      (J.degreeOf 1=1 ∨ NativeRoute F J ∨
        ∃ D, Irreducible D ∧ (D∣S.P ∨ D∣Sz.P) ∧
          rootEvaluation (carrierMap F) (ratio (carrierMap F) F) D=0 ∧ IsRelPrime J D) := by
  have hPs := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hsmall
    (by rw [hS.2.2.2.2.1]; omega)
  have hp3 : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣
      rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣ (asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hPs.2
  have heval : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) S.P=0 :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by decide : 3≠0)).trans hp3)
  obtain ⟨J,hJ,hJS,hJroot,hsplit⟩ := two_source_owner_split
    (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) S.P Sz.P
    (source_nonzero F S) (source_nonzero F Sz) heval
  refine ⟨J,hJ,hJS,hJroot,?_⟩
  rcases hsplit with huniq | hmixed
  · have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
      intro hz
      have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
      rw [hz,zero_dvd_iff] at hd
      exact hPs.1 hd
    have hdegree : 0<J.degreeOf 1 := by
      have hm := (Polynomial.rootMultiplicity_pos hJne).mpr hJroot
      have hh := Polynomial.natDegree_le_of_dvd
        ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
      simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
      have he : (rootPolynomialMap (carrierMap F) J).natDegree≤J.degreeOf 1 :=
        Polynomial.natDegree_map_le.trans_eq (asS_natDegree J)
      omega
    by_cases hl : J.degreeOf 1=1
    · exact Or.inl hl
    · exact Or.inr (Or.inl (unique_nonlinear_route F S Sz hS hZ hFT hpos hsmall
        J hJ hJS hJroot huniq.1 huniq.2.1 (by omega)))
  · exact Or.inr (Or.inr hmixed)

/-- The native factor needs no new leading-coefficient exclusion on a
curve where the original small source's leading coefficient is nonzero. -/
theorem factor_leading_dvd (J P : WholeSpaceCube6814.Poly (K:=K)) (hdiv : J∣P) :
    (asS J).leadingCoeff∣(asS P).leadingCoeff := by
  obtain ⟨Q,rfl⟩ := hdiv
  rw [map_mul,Polynomial.leadingCoeff_mul]
  exact dvd_mul_right _ _















end
end ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814


