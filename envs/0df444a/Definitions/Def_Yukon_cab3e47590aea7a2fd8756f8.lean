-- Prove2me | Definitions.Def_Yukon_cab3e47590aea7a2fd8756f8
-- name    : Yukon_cab3e47590aea7a2fd8756f8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T00:58:36.070013+00:00
-- url     : https://prove2.me/theorems/96d989e5-9b28-4459-b56c-1f7324788a9c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceGenericCuts6814.lean
--
--   yukon-proof-operation:certificate-tail-52e2be0f37080258eb5dea893db2bc561da795799b5bdc9340ddf2f770ca8d51
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODZlYjU0ZjQwNGUxMzdkYWU3NjAxNDc3YzYxMzEzNDI0MDNiYjIyYWY1Njg3OWFjZGFmNzFmZDdiMmRkNjA0OCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtNTJlMmJlMGYzNzA4MDI1OGViNWRlYTg5M2RiMmJjNTYxZGE3OTU3OTliNWJkYzkzNDBkZGYyZjc3MGNhOGQ1MSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2NhYjNlNDc1OTBhZWE3YTJmZDg3NTZmOCIsInYiOjJ9]

import Definitions.Def_Yukon_6db579f0800634a21a2958ad
















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The generic moving target is the actual affine target substitution.
Its ordinary clearing flags survive coefficient extension and gcd removal. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN095 RCN135 RCN136 RCN207
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814

variable (E : Type*) [Field E]

theorem genericTargetMap_C_X (i : Fin 3) :
    genericTargetMap E (Polynomial.C (MvPolynomial.X i))=MvPolynomial.X i := by
  have hi : (MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.X i))=
      MvPolynomial.X i.succ := by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_succ]
  change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hi,surfaceMap_X_succ]

theorem genericTargetMap_C (P : MvPolynomial (Fin 3) E) :
    genericTargetMap E (Polynomial.C P)=MvPolynomial.map (coefficientEmbedding E) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.C c))=
        MvPolynomial.C c := by
      apply (MvPolynomial.finSuccEquiv E 3).injective
      simp [MvPolynomial.finSuccEquiv_apply]
    change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
    rw [hc,surfaceMap_C,MvPolynomial.map_C]
    rfl
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,hP,genericTargetMap_C_X,MvPolynomial.map_X]

theorem genericTargetMap_X :
    genericTargetMap E Polynomial.X=MvPolynomial.C (initialCoordinate E) := by
  have hx : (MvPolynomial.finSuccEquiv E 3).symm Polynomial.X=MvPolynomial.X 0 := by
    apply (MvPolynomial.finSuccEquiv E 3).injective
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.finSuccEquiv_X_zero]
  change surfaceMap (polynomialEmbedding E) ((MvPolynomial.finSuccEquiv E 3).symm _)=_
  rw [hx,surfaceMap_X_zero]
  rfl

theorem genericTargetMap_eq_eval :
    genericTargetMap E=Polynomial.eval₂RingHom (MvPolynomial.map (coefficientEmbedding E))
      (MvPolynomial.C (initialCoordinate E)) := by
  apply Polynomial.ringHom_ext
  · intro P
    change genericTargetMap E (Polynomial.C P)=Polynomial.eval₂ _ _ (Polynomial.C P)
    rw [Polynomial.eval₂_C]
    exact genericTargetMap_C E P
  · change genericTargetMap E Polynomial.X=Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X]
    exact genericTargetMap_X E

section Sources
variable {K : Type*} [Field K]

theorem map_coefficients {L : Type*} [Field L] (f : E →+* L)
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K)) :
    (coefficients phi P).map (MvPolynomial.map f)=coefficients (f.comp phi) P := by
  have he : (MvPolynomial.map f).comp (surfaceMap phi)=surfaceMap (f.comp phi) := by
    apply RingHom.ext
    intro A
    simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]
  rw [coefficients,Polynomial.map_map,he]
  rfl

theorem generic_target_is_movingCut
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (s : ℕ) (quadratic A : MvPolynomial (Fin 3) E) :
    genericTargetMap E (targetPolynomial (coefficients phi P) s (2*A) quadratic)=
      movingCut ((coefficientEmbedding E).comp phi) P s
        (MvPolynomial.map (coefficientEmbedding E) quadratic)
        (MvPolynomial.map (coefficientEmbedding E) A) (initialCoordinate E) := by
  rw [genericTargetMap_eq_eval]
  change Polynomial.eval₂ _ _ (targetPolynomial _ _ _ _)=_
  rw [eval_targetPolynomial,map_coefficients]
  simp only [map_mul,map_ofNat,movingCut]

theorem generic_target_flag
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T s : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hsB : 2*s ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (quadratic A : MvPolynomial (Fin 3) E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag ⟨T-U,U-B+s,B⟩
      (genericTargetMap E (targetPolynomial (coefficients phi P) s (2*A) quadratic)) := by
  rw [generic_target_is_movingCut]
  exact movingCut_flag _ P B U T s hBU hUT hsB hP _ _ _
    (inFlag_map _ hQ) (inFlag_map _ hA)

end Sources

theorem flag_of_dvd (P Q : MvPolynomial (Fin 3) E) (p : FlagDegree)
    (hdiv : P ∣ Q) (hQ : Q≠0) (hflag : PolynomialInFlag p Q) : PolynomialInFlag p P := by
  have hw (w : Fin 3 → ℕ) (c : ℕ)
      (hc : ∀ e ∈ Q.support, Finsupp.weight w e ≤ c) :
      ∀ e ∈ P.support, Finsupp.weight w e ≤ c := by
    intro e he
    have h1 : Finsupp.weight w e ≤ weightedTotalDegree w P := Finset.le_sup he
    have h2 := RCN071.weightedTotalDegree_le_of_dvd_fin3 w P Q hdiv hQ
    have h3 : weightedTotalDegree w Q ≤ c := Finset.sup_le hc
    exact h1.trans (h2.trans h3)
  intro e he
  refine ⟨?_,?_,?_⟩
  · have hh := hw flagSWeights p.all (by
      intro d hd
      simpa [flag_weight_fin3,flagSWeights] using (hflag d hd).1) e he
    simpa [flag_weight_fin3,flagSWeights] using hh
  · have hh := hw flagYSWeights (p.yz+p.all) (by
      intro d hd
      simpa [flag_weight_fin3,flagYSWeights] using (hflag d hd).2.1) e he
    simpa [flag_weight_fin3,flagYSWeights] using hh
  · have hh := hw flagTotalWeights (p.zOnly+p.yz+p.all) (by
      intro d hd
      simpa [flag_weight_fin3,flagTotalWeights] using (hflag d hd).2.2) e he
    simpa [flag_weight_fin3,flagTotalWeights] using hh




section ActualPair
variable {K : Type*} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT




end ActualPair







end
end ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814


