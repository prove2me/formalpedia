-- Prove2me | Definitions.Def_Yukon_4ce2af81d75a1961b63d416a
-- name    : Yukon_4ce2af81d75a1961b63d416a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:10:13.736634+00:00
-- url     : https://prove2.me/theorems/90907285-822a-4b40-9fe9-cad0308ce051
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeHelperExistence.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeHelperExistence.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeHelperExistence.lean
--
--   yukon-proof-operation:foundation-direct-b2407dd669e2501b17b634d5f151058bfe8806cd8d5daf3668e78db0a9f93b87
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTEzZjNhOGQzMGVkMDg1YjE3ZWVlNmQ4NGY4YmM3NDBkMzI2ODdiOTliMGEyZmE4Zjc0MWQ3NWFkNzM2YTc0MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWIyNDA3ZGQ2NjllMjUwMWIxN2I2MzRkNWYxNTEwNThiZmU4ODA2Y2Q4ZDVkYWYzNjY4ZTc4ZGIwYTlmOTNiODciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl80Y2UyYWY4MWQ3NWExOTYxYjYzZDQxNmEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_cdab6a33f3f0c6c526308ae0














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

def NodeTarget {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :=
  RelativeJetTarget K (m:=m) (center K x u0 u1 F) (center_ne_zero K x u0 u1 hF)
    (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR

local instance nodeTargetAddCommGroup {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : AddCommGroup (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (AddCommGroup (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetModule {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : Module K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (Module K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetFinite {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) : Module.Finite K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) :=
  inferInstanceAs (Module.Finite K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR))

theorem nodeTarget_finrank {DF TF RF m L s : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :
    Module.finrank K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1) =
      localRankBound m L s-localRankBound (m-contactOrder K x u0 u1 F) (L-TF) (s-RF) := by
  change Module.finrank K (RelativeJetTarget K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR) = _
  rw [relativeJetTarget_finrank, center_contactOrder K x u0 u1 F hF]

def nodeJet (D w L s m : ℕ) (x u0 u1 : K) :
    globalCoefficientBox K D w L s →ₗ[K] LinearMap.range (boundedJetMap K m L s) :=
  LinearMap.codRestrict _
    ((contactSubmodule K 0 0 0 m).mkQ.comp
      ((center K x u0 u1).toLinearMap.comp (globalCoefficientBox K D w L s).subtype))
    (fun Q => jet_mem_range_of_globalBox K m ⟨center K x u0 u1 Q.val,
      center_globalBox K x u0 u1 Q⟩)

def nodeConstraint {DF TF RF m L s : ℕ} (D w : ℕ) (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) :
    globalCoefficientBox K D w L s →ₗ[K] NodeTarget K (m:=m) F hF hbox hT hR x u0 u1 :=
  (LinearMap.range (boundedFactorMap K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ.comp
      (nodeJet K D w L s m x u0 u1)

theorem nodeConstraint_zero_contact {DF TF RF m L s D w : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (x u0 u1 : K) (Q : globalCoefficientBox K D w L s)
    (hQ : nodeConstraint K (m:=m) D w F hF hbox hT hR x u0 u1 Q = 0) :
    RelativeContactAtLeast K x u0 u1 m F Q.val := by
  apply (center_relativeContact K x u0 u1 m F Q.val).mp
  apply (relative_contact_iff_jet_range K 0 0 0 m _ _
    (center_ne_zero K x u0 u1 hF)).mpr
  change (LinearMap.range (boundedFactorMap K (m:=m) (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF) (center_globalBox K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ
      (nodeJet K D w L s m x u0 u1 Q) = 0 at hQ
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hQ
  obtain ⟨v,hv⟩ := hQ
  exact ⟨v.val,congrArg Subtype.val hv⟩

def relativeConstraints {I : Type*} [Fintype I] {DF TF RF L s : ℕ}
    (D w : ℕ) (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (nodes u0 u1 : I → K) (m : I → ℕ) :
    globalCoefficientBox K D w L s →ₗ[K]
      ((i : I) → NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)) :=
  LinearMap.pi fun i => nodeConstraint K (m:=m i) D w F hF hbox hT hR (nodes i) (u0 i) (u1 i)

theorem relativeConstraints_zero_contact {I : Type*} [Fintype I] {DF TF RF L s D w : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (nodes u0 u1 : I → K) (m : I → ℕ) (Q : globalCoefficientBox K D w L s)
    (hQ : relativeConstraints K D w F hF hbox hT hR nodes u0 u1 m Q = 0) :
    ∀ i, RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q.val := by
  intro i
  exact nodeConstraint_zero_contact K F hF hbox hT hR (nodes i) (u0 i) (u1 i) Q
    (congrFun hQ i)

set_option maxHeartbeats 300000 in
public theorem exists_not_dvd_kernel
    {W : Type*} [AddCommGroup W] [Module K W] [Module.Finite K W]
    {TF RF D w L s nu : ℕ}
    (A : globalCoefficientBox K D w L s →ₗ[K] W)
    (F : Poly4 K) (hF : F ≠ 0)
    (hcode : nu ≤ wt (RCN081.contactWeights w) F)
    (htotal : TF ≤ wt RCN156.residualTotalWeights F)
    (hslope : RF ≤ wt RCN156.residualSWeights F)
    (hdim : coefficientCount (D-nu) w (L-TF) (s-RF) +
      Module.finrank K W < coefficientCount D w L s) :
    ∃ Q : globalCoefficientBox K D w L s, ¬ F ∣ Q.val ∧ A Q = 0 := by
  classical
  let V := LinearMap.ker A
  let recon : V →ₗ[K] Poly4 K := (globalCoefficientBox K D w L s).subtype.comp V.subtype
  have hrecon : Function.Injective recon := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  by_contra hnone
  have hdiv : ∀ v : V, F ∣ recon v := by
    intro v
    by_contra hv
    apply hnone
    exact ⟨v.val,hv,v.property⟩
  have hquot (v : V) : RCN180.quotientPolynomial recon F hdiv v ∈
      globalCoefficientBox K (D-nu) w (L-TF) (s-RF) := by
    let R := RCN180.quotientPolynomial recon F hdiv v
    have he : recon v = F*R := RCN180.recon_eq_mul_quotientPolynomial recon F hdiv v
    by_cases hz : R = 0
    · change R ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    have hn : recon v ≠ 0 := by rw [he]; exact mul_ne_zero hF hz
    exact RCN180.quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) F R D w L s nu TF RF hn hF hz v.val.property he hcode htotal hslope
  letI : Module.Finite K (globalCoefficientBox K (D-nu) w (L-TF) (s-RF)) :=
    RCN180.globalCoefficientBoxFinite (K:=K) (D-nu) w (L-TF) (s-RF)
  let divMap : V →ₗ[K] globalCoefficientBox K (D-nu) w (L-TF) (s-RF) :=
    LinearMap.codRestrict _ (RCN180.quotientLinear (K:=K) (V:=V) recon F hF hdiv)
      (fun v => by
        change RCN180.quotientPolynomial recon F hdiv v ∈ _
        exact hquot v)
  have hdivMap : Function.Injective divMap := by
    intro a b hab
    apply RCN180.quotientLinear_injective recon hrecon F hF hdiv
    exact congrArg Subtype.val hab
  have hupper : Module.finrank K V ≤
      Module.finrank K (globalCoefficientBox K (D-nu) w (L-TF) (s-RF)) :=
    LinearMap.finrank_le_finrank_of_injective (f:=divMap) hdivMap
  have hupperCount : Module.finrank K V ≤ coefficientCount (D-nu) w (L-TF) (s-RF) :=
    hupper.trans_eq (RCN180.globalCoefficientBox_finrank (K:=K) (D-nu) w (L-TF) (s-RF))
  have hnull : Module.finrank K A.range + Module.finrank K A.ker = coefficientCount D w L s :=
    A.finrank_range_add_finrank_ker.trans (RCN180.globalCoefficientBox_finrank (K:=K) D w L s)
  have hrange := A.range.finrank_le
  change Module.finrank K A.ker ≤ _ at hupperCount
  have hcount : coefficientCount D w L s ≤
      coefficientCount (D-nu) w (L-TF) (s-RF) + Module.finrank K W := by
    rw [← hnull]
    exact (Nat.add_le_add hrange hupperCount).trans_eq (Nat.add_comm _ _)
  exact (Nat.not_le_of_gt hdim) hcount

/-- A proper helper from the exact relative dimension inequality. The
factor is fixed across all nodes; no selected-factor or rank hypothesis
is smuggled into the conclusion. -/
theorem exists_proper_relative_helper
    {I : Type*} [Fintype I] {DF TF RF D w L s nu : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (hcode : nu ≤ wt (RCN081.contactWeights w) F)
    (htotal : TF ≤ wt RCN156.residualTotalWeights F)
    (hslope : RF ≤ wt RCN156.residualSWeights F)
    (nodes u0 u1 : I → K) (m : I → ℕ)
    (hdim : coefficientCount (D-nu) w (L-TF) (s-RF) +
      (∑ i : I, (localRankBound (m i) L s-
        localRankBound (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF))) <
      coefficientCount D w L s) :
    ∃ Q : Poly4 K, Q ∈ globalCoefficientBox K D w L s ∧ ¬ F ∣ Q ∧
      ∀ i, RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q := by
  classical
  let W := (i : I) → NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have htarget : Module.finrank K W =
      ∑ i : I, (localRankBound (m i) L s-
        localRankBound (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF)) := by
    change Module.finrank K ((i : I) → NodeTarget K (m:=m i) F hF hbox hT hR
      (nodes i) (u0 i) (u1 i)) = _
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact nodeTarget_finrank K F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have hd : coefficientCount (D-nu) w (L-TF) (s-RF) + Module.finrank K W <
      coefficientCount D w L s := by rw [htarget]; exact hdim
  obtain ⟨Q,hproper,hQ⟩ := exists_not_dvd_kernel K
    (relativeConstraints K D w F hF hbox hT hR nodes u0 u1 m) F hF hcode htotal hslope hd
  exact ⟨Q.val,Q.property,hproper,
    relativeConstraints_zero_contact K F hF hbox hT hR nodes u0 u1 m Q hQ⟩

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


