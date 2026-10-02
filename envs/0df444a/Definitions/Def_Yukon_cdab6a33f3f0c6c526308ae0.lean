-- Prove2me | Definitions.Def_Yukon_cdab6a33f3f0c6c526308ae0
-- name    : Yukon_cdab6a33f3f0c6c526308ae0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:52:10.102228+00:00
-- url     : https://prove2.me/theorems/557a009a-fc7d-457f-968b-e6e858585701
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCentering.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCentering.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCentering.lean
--
--   yukon-proof-operation:foundation-direct-06db8c89ea04b954624a1dd5f882bf4a0328b9a06c00d40ab95429e4de5e9d06
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTI5NDgwZDI0NDMyYjQxMmNlMzllZmRhZTVjNWE0NjQxMjM5NDZmOWE3ZTQ2YTVhZDU1MmE3MDA3MWE2NmQ4ZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTA2ZGI4Yzg5ZWEwNGI5NTQ2MjRhMWRkNWY4ODJiZjRhMDMyOGI5YTA2YzAwZDQwYWI5NTQyOWU0ZGU1ZTlkMDYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jZGFiNmEzM2YzZjBjNmM1MjYzMDhhZTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_52b2b488221380926e2e287b











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt wt_C wt_X wt_add_le wt_mul_le wt_pow_le)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def center (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0+MvPolynomial.C x,
    MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1,
    MvPolynomial.X 2, MvPolynomial.X 3]

theorem center_inverse (x u0 u1 : K) (Q : Poly4 K) :
    center K (-x) (-u0) (-u1) (center K x u0 u1 Q) = Q := by
  have he : (center K (-x) (-u0) (-u1)).comp (center K x u0 u1) =
      AlgHom.id K (Poly4 K) := by
    ext i
    fin_cases i <;> simp [center] <;> ring
  exact DFunLike.congr_fun he Q

theorem center_ne_zero (x u0 u1 : K) {Q : Poly4 K} (hQ : Q ≠ 0) :
    center K x u0 u1 Q ≠ 0 := by
  intro h
  have hc := congrArg (center K (-x) (-u0) (-u1)) h
  rw [center_inverse, map_zero] at hc
  exact hQ hc

theorem center_contact (x u0 u1 : K) (m : ℕ) (Q : Poly4 K) :
    ContactAtLeast K 0 0 0 m (center K x u0 u1 Q) ↔
      ContactAtLeast K x u0 u1 m Q := by
  have he : (localize K 0 0 0).comp (center K x u0 u1) = localize K x u0 u1 := by
    ext i
    fin_cases i <;> simp [center,localize,localVariables] <;> ring
  unfold ContactAtLeast
  rw [show localize K 0 0 0 (center K x u0 u1 Q) = localize K x u0 u1 Q from
    DFunLike.congr_fun he Q]

theorem center_contactOrder (x u0 u1 : K) (Q : Poly4 K) (hQ : Q ≠ 0) :
    contactOrder K 0 0 0 (center K x u0 u1 Q) = contactOrder K x u0 u1 Q := by
  apply Nat.le_antisymm
  · apply (contactAtLeast_iff_le K x u0 u1 _ Q hQ).mp
    apply (center_contact K x u0 u1 _ Q).mp
    exact (contactAtLeast_iff_le K 0 0 0 _ _ (center_ne_zero K x u0 u1 hQ)).mpr le_rfl
  · apply (contactAtLeast_iff_le K 0 0 0 _ _ (center_ne_zero K x u0 u1 hQ)).mp
    apply (center_contact K x u0 u1 _ Q).mpr
    exact (contactAtLeast_iff_le K x u0 u1 _ Q hQ).mpr le_rfl

theorem algHom_weight_le (phi : Poly4 K →ₐ[K] Poly4 K) (w : Fin 4 → ℕ)
    (hvar : ∀ i, wt w (phi (MvPolynomial.X i)) ≤ w i) (Q : Poly4 K) :
    wt w (phi Q) ≤ wt w Q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q, map_sum]
  apply RCN235.wt_finset_sum_le
  intro d hd
  have hp (i : Fin 4) : wt w (phi (MvPolynomial.X i)^d i) ≤ d i*w i :=
    (wt_pow_le w _ _).trans (Nat.mul_le_mul_left _ (hvar i))
  have hm := wt_mul_le w (MvPolynomial.C (Q.coeff d)) (phi (MvPolynomial.X 0)^d 0)
  have hm1 := wt_mul_le w (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0)
    (phi (MvPolynomial.X 1)^d 1)
  have hm2 := wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1)
    (phi (MvPolynomial.X 2)^d 2)
  have hm3 := wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1*
      phi (MvPolynomial.X 2)^d 2) (phi (MvPolynomial.X 3)^d 3)
  have hc : phi (MvPolynomial.C (Q.coeff d)) = MvPolynomial.C (Q.coeff d) := phi.commutes _
  rw [RCN122.monomial_eq K, map_mul, map_mul, map_mul, map_mul, hc]
  simp only [map_pow]
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  rw [wt_C] at hm
  have hbound := MvPolynomial.le_weightedTotalDegree w hd
  rw [RCN081.weight_fin4] at hbound
  change _ ≤ wt w Q at hbound
  omega

theorem center_weight_le (x u0 u1 : K) (w : Fin 4 → ℕ) (hw : w 3 ≤ w 1) (Q : Poly4 K) :
    wt w (center K x u0 u1 Q) ≤ wt w Q := by
  apply algHom_weight_le
  intro i
  simp only [center, MvPolynomial.aeval_X]
  fin_cases i
  · change wt w (MvPolynomial.X 0+MvPolynomial.C x) ≤ w 0
    exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
  · change wt w (MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1) ≤ w 1
    apply (wt_add_le w _ _).trans
    apply max_le
    · exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
    · exact (wt_mul_le w _ _).trans (by simpa [wt_X,wt_C] using hw)
  · change wt w (MvPolynomial.X 2 : Poly4 K) ≤ w 2
    rw [wt_X]
  · change wt w (MvPolynomial.X 3 : Poly4 K) ≤ w 3
    rw [wt_X]

theorem center_globalBox {D w L s : ℕ} (x u0 u1 : K)
    (Q : globalCoefficientBox K D w L s) :
    center K x u0 u1 Q.val ∈ globalCoefficientBox K D w L s := by
  by_cases hz : Q.val = 0
  · rw [hz,map_zero]; exact Submodule.zero_mem _
  obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hz
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) (Q.property hd).2.2
  have hb := (RCN180.mem_flagGlobalCoefficientBox_iff Q.val D w L s hD).mp Q.property
  apply (RCN180.mem_flagGlobalCoefficientBox_iff _ D w L s hD).mpr
  refine ⟨(center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.1,
    (center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.2.1,
    (center_weight_le K x u0 u1 _ ?_ Q.val).trans hb.2.2⟩
  all_goals simp [RCN156.residualTotalWeights,RCN156.residualSWeights,RCN081.contactWeights]

theorem center_relativeContact (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) :
    RelativeContactAtLeast K 0 0 0 m (center K x u0 u1 F) (center K x u0 u1 Q) ↔
      RelativeContactAtLeast K x u0 u1 m F Q := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨center K (-x) (-u0) (-u1) B,?_⟩
    apply (center_contact K x u0 u1 m _).mp
    rw [map_sub,map_mul]
    have he : center K x u0 u1 (center K (-x) (-u0) (-u1) B) = B := by
      simpa using center_inverse K (-x) (-u0) (-u1) B
    rw [he]
    exact hB
  · rintro ⟨B,hB⟩
    refine ⟨center K x u0 u1 B,?_⟩
    rw [← map_mul,← map_sub]
    exact (center_contact K x u0 u1 m _).mpr hB

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


