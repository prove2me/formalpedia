-- Prove2me | Definitions.Def_Yukon_10805ee98000946934f31f50
-- name    : Yukon_10805ee98000946934f31f50
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T00:20:51.50779+00:00
-- url     : https://prove2.me/theorems/ccdfdb0d-6ce3-4f03-a242-f00554c6c1ee
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceGenericField6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceGenericField6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceGenericField6814.lean
--
--   yukon-proof-operation:certificate-tail-7c681378c277e85c54e847dafe6544f1c5b3886dbc143904dbc826813f8c5e59
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTBlYjk5MzI1NGM5NmJjYWU5NmE3Yzc5ODU1YWUxNmVhNjc1YTJmOGRlOWE0MmE2MjkxYTMyN2E3YjliYjk0MSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtN2M2ODEzNzhjMjc3ZTg1YzU0ZTg0N2RhZmU2NTQ0ZjFjNWIzODg2ZGJjMTQzOTA0ZGJjODI2ODEzZjhjNWU1OSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzEwODA1ZWU5ODAwMDk0NjkzNGYzMWY1MCIsInYiOjJ9]

import Definitions.Def_Yukon_55fad66368719f3e76698681

import Mathlib.RingTheory.Flat.Localization















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Properness of the actual five-variable source pair after freezing the
code variable in the repository's canonical generic field. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGenericField6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN135 MovingSourceFlatBaseChange6814 MovingSourceClearing6814

variable (K : Type*) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem generic_coefficient_map_relPrime {σ : Type*} [Finite σ]
    (P Q : MvPolynomial σ (Polynomial K)) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (MvPolynomial.map (polynomialEmbedding K) P)
      (MvPolynomial.map (polynomialEmbedding K) Q) := by
  letI : Module.Flat (Polynomial K) (RationalBase K) :=
    IsLocalization.flat (RationalBase K) (nonZeroDivisors (Polynomial K))
  letI : Module.Flat (Polynomial K) (GenericField K) :=
    Module.Flat.trans (Polynomial K) (RationalBase K) (GenericField K)
  letI : Module.Flat (MvPolynomial σ (Polynomial K)) (MvPolynomial σ (GenericField K)) :=
    coefficient_map_flat
  have hemb : polynomialEmbedding K=algebraMap (Polynomial K) (GenericField K) :=
    (IsScalarTower.algebraMap_eq (Polynomial K) (RationalBase K) (GenericField K)).symm
  rw [hemb]
  exact map_isRelPrime_of_flat (MvPolynomial.map_injective _ (by rw [←hemb]; exact polynomialEmbedding_injective K)) P Q hP hrel

def collectCode : WholeSpaceCube6814.Poly (K := K) ≃ₐ[K] MvPolynomial (Fin 4) (Polynomial K) :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 4)).trans
    (MvPolynomial.optionEquivRight K (Fin 4))

def sourceMap {E : Type*} [Field E] (phi : Polynomial K →+* E) :
    WholeSpaceCube6814.Poly (K := K) →+* MvPolynomial (Fin 4) E :=
  (MvPolynomial.map phi).comp (collectCode K).toRingHom

abbrev genericSourceMap := sourceMap K (polynomialEmbedding K)

theorem sourceMap_X_zero {E : Type*} [Field E] (phi : Polynomial K →+* E) :
    sourceMap K phi (MvPolynomial.X 0)=MvPolynomial.C (phi Polynomial.X) := by
  simp [sourceMap,collectCode,MvPolynomial.renameEquiv_apply]

theorem sourceMap_X_succ {E : Type*} [Field E] (phi : Polynomial K →+* E) (i : Fin 4) :
    sourceMap K phi (MvPolynomial.X i.succ)=MvPolynomial.X i := by
  simp [sourceMap,collectCode,MvPolynomial.renameEquiv_apply]

theorem asS_X_code : SecondJetCoefficients.asS (MvPolynomial.X (0 : Fin 5) : WholeSpaceCube6814.Poly (K := K))=
    Polynomial.C (MvPolynomial.X 0) := by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  change MvPolynomial.finSuccEquiv K 4 (MvPolynomial.X (0 : Fin 4).succ)=_
  exact MvPolynomial.finSuccEquiv_X_succ

theorem asS_X_jet : SecondJetCoefficients.asS (MvPolynomial.X (1 : Fin 5) : WholeSpaceCube6814.Poly (K := K))=
    Polynomial.X := by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  change MvPolynomial.finSuccEquiv K 4 (MvPolynomial.X 0)=_
  exact MvPolynomial.finSuccEquiv_X_zero

theorem asS_X_tail (i : Fin 3) :
    SecondJetCoefficients.asS (MvPolynomial.X i.succ.succ : WholeSpaceCube6814.Poly (K := K))=
      Polynomial.C (MvPolynomial.X i.succ) := by
  simp only [SecondJetCoefficients.asS,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  have h0 : i.succ.succ ≠ (0 : Fin 5) := by fin_cases i <;> decide
  have h1 : i.succ.succ ≠ (1 : Fin 5) := by fin_cases i <;> decide
  rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem genericSourceMap_relPrime (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hrel : IsRelPrime J Q) : IsRelPrime (genericSourceMap K J) (genericSourceMap K Q) := by
  have hJ' : collectCode K J≠0 := by
    intro hz
    exact hJ ((collectCode K).injective (by simpa only [map_zero] using hz))
  exact generic_coefficient_map_relPrime K _ _ hJ'
    (isRelPrime_equiv (collectCode K).toRingEquiv J Q hrel)

theorem view_sourceMap {E : Type*} [Field E] (phi : Polynomial K →+* E)
    (P : WholeSpaceCube6814.Poly (K := K)) :
    MvPolynomial.finSuccEquiv E 3 (sourceMap K phi P)=coefficients phi P := by
  have hx (i : Fin 5) : MvPolynomial.finSuccEquiv E 3 (sourceMap K phi (MvPolynomial.X i))=
      coefficients phi (MvPolynomial.X i) := by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rw [sourceMap_X_zero,coefficients,asS_X_code,Polynomial.map_C,RCN136.surfaceMap_X_zero]
      simp [MvPolynomial.finSuccEquiv_apply]
    · rw [sourceMap_X_succ,MvPolynomial.finSuccEquiv_X_zero,coefficients]
      rw [show (0 : Fin 4).succ=(1 : Fin 5) by decide,asS_X_jet,Polynomial.map_X]
    · rw [sourceMap_X_succ,MvPolynomial.finSuccEquiv_X_succ,coefficients,asS_X_tail,
        Polynomial.map_C,RCN136.surfaceMap_X_succ]
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [sourceMap,collectCode,coefficients,SecondJetCoefficients.asS,
      MvPolynomial.renameEquiv_apply,MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ =>
    simp only [map_add,coefficients,Polynomial.map_add] at hP hQ ⊢
    rw [hP,hQ]
  | mul_X P i hP =>
    have hi := hx i
    dsimp only [coefficients] at hi
    simp only [map_mul,coefficients,Polynomial.map_mul] at hP ⊢
    rw [hP,hi]

theorem generic_coefficients_relPrime (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hrel : IsRelPrime J Q) :
    IsRelPrime (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) Q) := by
  have h := isRelPrime_equiv (MvPolynomial.finSuccEquiv (GenericField K) 3).toRingEquiv
    (genericSourceMap K J) (genericSourceMap K Q) (genericSourceMap_relPrime K J Q hJ hrel)
  change IsRelPrime (MvPolynomial.finSuccEquiv (GenericField K) 3 (sourceMap K (polynomialEmbedding K) J))
    (MvPolynomial.finSuccEquiv (GenericField K) 3 (sourceMap K (polynomialEmbedding K) Q)) at h
  simpa only [view_sourceMap] using h





end
end ProximityPrize.SubmissionLower.MovingSourceGenericField6814


