-- Prove2me | Definitions.Def_Yukon_9113295e0811404ee8840e2e
-- name    : Yukon_9113295e0811404ee8840e2e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:39:50.413627+00:00
-- url     : https://prove2.me/theorems/8b15e55e-10cb-49a6-b13f-3869de792ee2
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeContactCap.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeContactCap.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeContactCap.lean
--
--   yukon-proof-operation:foundation-direct-8c05c8a45ebf01e6970fba9b0a937a7d55cabde4522740be54689eae4a8df7a4
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzYzOTYwZGM1NDA1Y2EyYTk4Nzg0ZGM1MjQ4YTJhZjgxNTllNmQwMzgyZTYyZDczYTNiNjQxNGU5NWY0ZWU1MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LThjMDVjOGE0NWViZjAxZTY5NzBmYmE5YjBhOTM3YTdkNTVjYWJkZTQ1MjI3NDBiZTU0Njg5ZWFlNGE4ZGY3YTQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85MTEzMjk1ZTA4MTE0MDRlZTg4NDBlMmUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_09ab13a9a212414cf02cb11d













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814 RelativeContactRank6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K : Type*) [Field K]

theorem homogenized_zero_eq (F : Poly4 K) :
    homogenizedTranslation K 0 0 0 F =
      MvPolynomial.finSuccEquiv K 3 (contactBlowup K F) := by
  have hX1 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(0 : Fin 3))
  have hX2 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(1 : Fin 3))
  have hX3 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) := MvPolynomial.finSuccEquiv_X_succ (j:=(2 : Fin 3))
  have hgen (i : Fin 4) :
      homogenizedTranslation K 0 0 0 (MvPolynomial.X i) =
        MvPolynomial.finSuccEquiv K 3 (contactBlowup K (MvPolynomial.X i)) := by
    rw [contactBlowup_X]
    fin_cases i <;> simp [homogenizedTranslation,translationVariables,seedAffine,
      MvPolynomial.finSuccEquiv_X_zero,hX1,hX2,hX3]
  induction F using MvPolynomial.induction_on with
  | C a => simp [homogenizedTranslation, MvPolynomial.finSuccEquiv_apply,
      Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F i hF => simpa only [map_mul] using congrArg₂ (· * ·) hF (hgen i)

theorem translated_zero_coeff (F : Poly4 K) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d.tail
        ((homogenizedTranslation K 0 0 0 F).coeff (d 0+d 1)) = MvPolynomial.coeff d F := by
  rw [homogenized_zero_eq, MvPolynomial.finSuccEquiv_coeff_coeff]
  have he : Finsupp.cons (d 0+d 1) d.tail = blowupExponent d := by
    ext i
    fin_cases i <;> simp [blowupExponent] <;> rfl
  rw [he]
  change Finsupp.mapDomain blowupExponent (AddMonoidAlgebra.coeff F) (blowupExponent d) = _
  exact Finsupp.mapDomain_apply blowupExponent_injective _ _

/-- Excess contact would force an X-factor. This uses actual coefficient
blocks, so cancellation between Taylor blocks cannot evade the bound. -/
theorem X_dvd_of_contact_large {DF T R B : ℕ} (F : Poly4 K)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hY : F.degreeOf 1 ≤ B)
    (hcontact : ContactAtLeast K 0 0 0 (B+R+1) F) :
    MvPolynomial.X (0 : Fin 4) ∣ F := by
  classical
  let m := B+R+1
  have hz (n : ℕ) (hn : n ≤ B) : (homogenizedTranslation K 0 0 0 F).coeff n = 0 := by
    have hnm : n < m := by dsimp [m]; omega
    let p := blocksOf K m (⟨F,hbox⟩ : globalCoefficientBox K DF 1 T R) ⟨n,hnm⟩
    have hp : (blockJet K (min n T) T R (m-n)) p = 0 := by
      change contactJet K (m-n) p.val = 0
      apply (contactJet_eq_zero_iff K (m-n) _).mpr
      rw [blocksOf_coeff]
      exact (contactAtLeast_iff_block_divisibility K 0 0 0 m F).mp hcontact n
    have hker : p ∈ LinearMap.ker (blockJet K (min n T) T R (m-n)) := hp
    rw [blockJet_kernel_eq_bot_of_large K (min n T) T R (m-n)
      (Or.inr (by dsimp [m]; omega))] at hker
    have hp0 : p = 0 := by simpa using hker
    have he := congrArg Subtype.val hp0
    rw [blocksOf_coeff] at he
    exact he
  have hc (d : Fin 4 →₀ ℕ) (hd : d 0 = 0) : MvPolynomial.coeff d F = 0 := by
    by_contra hne
    have hd1 := MvPolynomial.degreeOf_le_iff.mp hY d (MvPolynomial.mem_support_iff.mpr hne)
    have he := translated_zero_coeff K F d
    rw [hd,zero_add,hz (d 1) hd1,MvPolynomial.coeff_zero] at he
    exact hne he.symm
  have hdiv : Polynomial.X ∣ MvPolynomial.finSuccEquiv K 3 F := by
    apply Polynomial.X_dvd_iff.mpr
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_zero]
    exact hc (Finsupp.cons 0 d) rfl
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨(MvPolynomial.finSuccEquiv K 3).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simpa only [map_mul,MvPolynomial.finSuccEquiv_X_zero,AlgEquiv.apply_symm_apply] using hQ

theorem contactOrder_le_of_X_not_dvd {DF T R B : ℕ} (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hY : F.degreeOf 1 ≤ B)
    (hX : ¬ MvPolynomial.X (0 : Fin 4) ∣ F) : contactOrder K 0 0 0 F ≤ B+R := by
  by_contra h
  apply hX
  apply X_dvd_of_contact_large K F hbox hY
  exact (contactAtLeast_iff_le K 0 0 0 (B+R+1) F hF).mpr (by omega)

def centerEquiv (x u0 u1 : K) : Poly4 K ≃ₐ[K] Poly4 K :=
  AlgEquiv.ofAlgHom (center K x u0 u1) (center K (-x) (-u0) (-u1))
    (by
      apply DFunLike.ext
      intro Q
      change center K x u0 u1 (center K (-x) (-u0) (-u1) Q) = Q
      simpa using center_inverse K (-x) (-u0) (-u1) Q)
    (by
      apply DFunLike.ext
      intro Q
      exact center_inverse K x u0 u1 Q)

theorem X_not_dvd_center_of_irreducible (F : Poly4 K) (hF : Irreducible F)
    (hR : 0 < F.degreeOf 2) (x u0 u1 : K) :
    ¬ MvPolynomial.X (0 : Fin 4) ∣ center K x u0 u1 F := by
  intro hdiv
  let E := centerEquiv K (-x) (-u0) (-u1)
  have hp : Irreducible (E (MvPolynomial.X (0 : Fin 4))) :=
    (MulEquiv.irreducible_iff (f:=E.toMulEquiv)).mpr (MvPolynomial.X_prime.irreducible)
  have hd : E (MvPolynomial.X (0 : Fin 4)) ∣ F := by
    have hm := map_dvd E.toRingHom hdiv
    change center K (-x) (-u0) (-u1) (MvPolynomial.X (0 : Fin 4)) ∣
      center K (-x) (-u0) (-u1) (center K x u0 u1 F) at hm
    rw [center_inverse] at hm
    exact hm
  have hd' := (hp.associated_of_dvd hF hd).symm.dvd
  have hle := RCN081.degreeOf_le_of_dvd (2 : Fin 4) F _ hd' hp.ne_zero
  have he : E (MvPolynomial.X (0 : Fin 4)) = MvPolynomial.X 0+MvPolynomial.C (-x) := by
    simp [E,centerEquiv,center]
  rw [he] at hle
  have hh := MvPolynomial.degreeOf_add_le (2 : Fin 4)
    (MvPolynomial.X 0 : Poly4 K) (MvPolynomial.C (-x))
  have hh0 : (MvPolynomial.X 0+MvPolynomial.C (-x) : Poly4 K).degreeOf 2 ≤ 0 := by
    simpa [MvPolynomial.degreeOf_X] using hh
  omega

/-- The finite contact cap required by the saved profiles, for the actual
irreducible positive-slope factor at every received affine value. -/
theorem contactOrder_le_middle_add_slope {DF T R B : ℕ} (F : Poly4 K)
    (hF : Irreducible F) (hR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : RCN234.wt RCN156.residualYSWeights F ≤ B) (x u0 u1 : K) :
    contactOrder K x u0 u1 F ≤ B+R := by
  rw [← center_contactOrder K x u0 u1 F hF.ne_zero]
  apply contactOrder_le_of_X_not_dvd K (center K x u0 u1 F)
    (center_ne_zero K x u0 u1 hF.ne_zero) (center_globalBox K x u0 u1 ⟨F,hbox⟩)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hw := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd).trans
      ((center_weight_le K x u0 u1 RCN156.residualYSWeights (by decide) F).trans hB)
    rw [RCN081.weight_fin4] at hw
    simp only [RCN156.residualYSWeights] at hw
    simp at hw
    omega
  · exact X_not_dvd_center_of_irreducible K F hF hR x u0 u1

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


