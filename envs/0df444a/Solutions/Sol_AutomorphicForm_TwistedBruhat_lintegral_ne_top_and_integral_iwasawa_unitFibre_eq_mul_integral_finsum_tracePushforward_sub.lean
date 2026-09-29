-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5f3c79a6-f7c9-5f36-ad94-f71f0397b472

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_UnipotentTermCuspBound_exists_forall_setLIntegral_tsum_setLIntegral_enorm_mul_tsum_tsum_enorm_sub_ne_top
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
import Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward
import Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory NumberField
open scoped Pointwise ENNReal

noncomputable section

namespace R1FibreUnfold

section Basic

open AutomorphicForm AutomorphicForm.TwistedBruhat IsDedekindDomain
open scoped TensorProduct

theorem isFactorizableTestFn_of_isSemiLocalFactorization (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (S : Finset (HeightOneSpectrum (𝓞 K))) {φ : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsSemiLocalFactorization K L S φ φa φf φS) : IsFactorizableTestFn L φ :=
  ⟨φa, φf, h.1, h.2.1, h.2.2.2.2.2⟩

theorem exists_isCuspTransversal (L : Type) [Field L] :
    ∃ reps : Set (GL (Fin 2) L), IsCuspTransversal L reps := by
  refine ⟨Set.range fun q : Quotient (QuotientGroup.rightRel (borelSubgroup L)) => q.out, fun g => ?_⟩
  refine ⟨(Quotient.mk (QuotientGroup.rightRel (borelSubgroup L)) g).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact (QuotientGroup.rightRel_apply (s := borelSubgroup L)).mp (Quotient.mk_out g)
  · rintro ρ ⟨⟨q, rfl⟩, hq⟩
    have h1 : Quotient.mk (QuotientGroup.rightRel (borelSubgroup L)) q.out =
        Quotient.mk (QuotientGroup.rightRel (borelSubgroup L)) g :=
      Quotient.sound ((QuotientGroup.rightRel_apply (s := borelSubgroup L)).mpr hq)
    rw [Quotient.out_eq] at h1
    rw [h1]

end Basic

section CuspIndex

open LT.TwistedNorm AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem twistedConj_mem_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (b : GL (Fin 2) L) {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) :
    b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hclass⟩ := hδ
  refine ⟨γ, hγ, ?_⟩
  have hmk : SigmaConjClasses.mk σ δ =
      SigmaConjClasses.mk σ (b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) :=
    SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨b, rfl⟩
  rw [← hmk]
  exact hclass

theorem bijOn_twistedConj_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (b : GL (Fin 2) L) :
    Set.BijOn (fun δ : GL (Fin 2) L => b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b)
      (normUnipotentSet K L σ hgen) (normUnipotentSet K L σ hgen) := by
  refine ⟨fun δ hδ => twistedConj_mem_normUnipotentSet hgen b hδ, fun δ _ δ' _ hh => ?_, fun δ hδ => ?_⟩
  · have := congrArg (fun y => b * y * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹) hh
    simpa [mul_assoc] using this
  · refine ⟨b * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹, ?_, by group⟩
    have h := twistedConj_mem_normUnipotentSet hgen b⁻¹ hδ
    rwa [inv_inv, map_inv] at h

end CuspIndex

section UpperTriangular

open AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem mul_apply_one_zero_of_upper {g h : GL (Fin 2) L}
    (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]; ring

theorem mul_apply_zero_zero_of_upper (g : GL (Fin 2) L) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]; ring

theorem mul_apply_one_one_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg]; ring

theorem apply_one_one_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem apply_zero_zero_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem inv_apply_one_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
  (borelSubgroup L).inv_mem hg

theorem inv_apply_one_one_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = ((g : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ := by
  have h := mul_apply_one_one_of_upper (inv_apply_one_zero_of_upper hg) g
  rw [inv_mul_cancel] at h
  have h1 : ((1 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem inv_apply_zero_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((g : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ := by
  have h := mul_apply_zero_zero_of_upper g⁻¹ hg
  rw [inv_mul_cancel] at h
  have h1 : ((1 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by simp
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem map_apply' (σ : L →+* L) (g : GL (Fin 2) L) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map σ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      σ ((g : Matrix (Fin 2) (Fin 2) L) i j) := rfl

variable (L) in

def fib (p q : L) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = p ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = q}

theorem twistedConj_mem_fib (σ : L →+* L) {b : GL (Fin 2) L} (hb : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    {p q : L} {δ : GL (Fin 2) L} (hδ : δ ∈ fib L p q) :
    b⁻¹ * δ * Matrix.GeneralLinearGroup.map σ b ∈
      fib L (p * (σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1))
        (q * (σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0)) := by
  obtain ⟨hδ0, hδ1, hδ2⟩ := hδ
  have hσb : ((Matrix.GeneralLinearGroup.map σ b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    rw [map_apply', hb, map_zero]
  have hbi := inv_apply_one_zero_of_upper hb
  have hbd : ((b⁻¹ * δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := mul_apply_one_zero_of_upper hbi hδ0
  refine ⟨mul_apply_one_zero_of_upper hbd hσb, ?_, ?_⟩
  · rw [mul_apply_one_one_of_upper hbd, mul_apply_one_one_of_upper hbi, inv_apply_one_one_of_upper hb, hδ1,
      map_apply', div_eq_mul_inv]
    ring
  · rw [mul_apply_zero_zero_of_upper _ hσb, mul_apply_zero_zero_of_upper _ hδ0, inv_apply_zero_zero_of_upper hb,
      hδ2, map_apply', div_eq_mul_inv]
    ring

theorem bijOn_twistedConj_fib (σ : L →+* L) {b : GL (Fin 2) L} (hb : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (p q p' q' : L)
    (hp' : p' = p * (σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1))
    (hq' : q' = q * (σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0)) :
    Set.BijOn (fun δ : GL (Fin 2) L => b⁻¹ * δ * Matrix.GeneralLinearGroup.map σ b) (fib L p q) (fib L p' q') := by
  subst hp' hq'
  have h11 : (b : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := apply_one_one_ne_zero_of_upper hb
  have h00 : (b : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := apply_zero_zero_ne_zero_of_upper hb
  have hσ11 : σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).mpr h11
  have hσ00 : σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := (map_ne_zero σ).mpr h00
  refine ⟨fun δ hδ => twistedConj_mem_fib σ hb hδ, fun δ _ δ' _ hh => ?_, fun δ hδ => ?_⟩
  · have := congrArg (fun y => b * y * (Matrix.GeneralLinearGroup.map σ b)⁻¹) hh
    simpa [mul_assoc] using this
  · refine ⟨b * δ * (Matrix.GeneralLinearGroup.map σ b)⁻¹, ?_, by group⟩
    have h := twistedConj_mem_fib σ (inv_apply_one_zero_of_upper hb) hδ
    rw [inv_inv, map_inv, inv_apply_one_one_of_upper hb, inv_apply_zero_zero_of_upper hb] at h
    convert h using 2
    · (try simp only [map_inv₀]); field_simp
    · (try simp only [map_inv₀]); field_simp

theorem mul_mem_fib_of_unipotent {p q : L} {δ m : GL (Fin 2) L} (hδ : δ ∈ fib L p q)
    (hm0 : (m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hm1 : (m : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (hm2 : (m : Matrix (Fin 2) (Fin 2) L) 0 0 = 1) : δ * m ∈ fib L p q := by
  obtain ⟨hδ0, hδ1, hδ2⟩ := hδ
  refine ⟨mul_apply_one_zero_of_upper hδ0 hm0, ?_, ?_⟩
  · rw [mul_apply_one_one_of_upper hδ0, hδ1, hm1, mul_one]
  · rw [mul_apply_zero_zero_of_upper _ hm0, hδ2, hm2, mul_one]

theorem bijOn_mul_fib_of_unipotent (p q : L) {m : GL (Fin 2) L}
    (hm0 : (m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hm1 : (m : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (hm2 : (m : Matrix (Fin 2) (Fin 2) L) 0 0 = 1) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * m) (fib L p q) (fib L p q) := by
  have hi0 : ((m⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := inv_apply_one_zero_of_upper hm0
  have hi1 : ((m⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
    rw [inv_apply_one_one_of_upper hm0, hm1, inv_one]
  have hi2 : ((m⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    rw [inv_apply_zero_zero_of_upper hm0, hm2, inv_one]
  refine ⟨fun δ hδ => mul_mem_fib_of_unipotent hδ hm0 hm1 hm2, fun δ _ δ' _ h => mul_right_cancel h,
    fun δ hδ => ?_⟩
  exact ⟨δ * m⁻¹, mul_mem_fib_of_unipotent hδ hi0 hi1 hi2, by simp⟩

theorem map_unipotentGL2 (f : L →+* L) (l : L) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 l) = unipotentGL2 (f l) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [map_apply', unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem norm_inv' {x : L} (hx : x ≠ 0) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])

end UpperTriangular

section AdelicAlgebra

open AutomorphicForm IsDedekindDomain

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem conj_identity (h δ : GL (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L) :
    (globalPoints (𝓞 L) L h * x)⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y =
      x⁻¹ * globalPoints (𝓞 L) L (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) *
        sigmaAdelicAct K L D σ ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  rw [map_mul (sigmaAdelicAct K L D σ), map_inv (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints',
    map_mul (globalPoints (𝓞 L) L), map_mul (globalPoints (𝓞 L) L), map_inv (globalPoints (𝓞 L) L), mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem globalPoints_unipotentGL2 (l : L) :
    globalPoints (𝓞 L) L (unipotentGL2 l) = unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show algebraMap L (AdeleRing (𝓞 L) L) ((unipotentGL2 l : Matrix (Fin 2) (Fin 2) L) i j) =
    (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_mul_globalPoints {h : GL (Fin 2) L} (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (q : AdeleRing (𝓞 L) L) :
    unipotentGL2 q * globalPoints (𝓞 L) L h =
      globalPoints (𝓞 L) L h *
        unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L)
          ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0) * q) := by
  have h00 : (h : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h0
    have hdet := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two, hh, h0] at hdet
    simp at hdet
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hg : ∀ i j, ((globalPoints (𝓞 L) L h : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
  have e : algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 0 0) *
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0) =
      algebraMap L (AdeleRing (𝓞 L) L) ((h : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [← map_mul, mul_div_cancel₀ _ h00]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh, unipotentGL2_coe]
  · rw [← mul_assoc, e]
    ring

end AdelicAlgebra

section Box

open AutomorphicForm IsDedekindDomain NumberField.AdelicHaar NumberField.AdelicBox

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem borelSpace_adele : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L

attribute [local instance] borelSpace_adele

scoped instance isAddHaarMeasure_adelicAddHaar' : (adelicAddHaar (𝓞 L) L).IsAddHaarMeasure :=
  isAddHaarMeasure_adelicAddHaar (𝓞 L) L

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  unfold adelicAddHaar; infer_instance

theorem measurePreserving_smul_principal (q : Lˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 L) L =>
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) • x) (adelicAddHaar (𝓞 L) L)
      (adelicAddHaar (𝓞 L) L) := by
  set u := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)
  refine ⟨measurable_const_smul u, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_smul u) hs, Set.preimage_smul,
    ← distribHaarChar_mul (adelicAddHaar (𝓞 L) L) u⁻¹ s, map_inv]
  have : distribHaarChar (AdeleRing (𝓞 L) L) u = 1 := NumberField.AdeleRing.distribHaarChar_algebraMap L q
  rw [this, inv_one, ENNReal.coe_one, one_mul]

theorem integral_cond_adelicBox_comp_smul (h : AdeleRing (𝓞 L) L → ℂ)
    (hper : ∀ (l : L) (x : AdeleRing (𝓞 L) L), h (algebraMap L (AdeleRing (𝓞 L) L) l + x) = h x) (q : Lˣ) :
    ∫ x, h ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) • x)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) =
      ∫ x, h x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) := by
  set u := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)
  set μ := adelicAddHaar (𝓞 L) L with hμ
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  congr 1
  have hmp := measurePreserving_smul_principal L q
  let e : AdeleRing (𝓞 L) L ≃ᵐ AdeleRing (𝓞 L) L := (Homeomorph.smul u).toMeasurableEquiv
  have he : (e : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = fun x => u • x := rfl
  have hmpe : MeasurePreserving e μ μ := hmp
  have h1 : ∫ x in adelicBox L, h (u • x) ∂μ = ∫ y in e '' adelicBox L, h y ∂μ :=
    (hmpe.setIntegral_image_emb e.measurableEmbedding h (adelicBox L)).symm
  rw [h1]
  set G := AdeleRing.principalSubgroup (𝓞 L) L with hG
  have hB : IsAddFundamentalDomain G (adelicBox L) μ := isAddFundamentalDomain_adelicBox L μ
  let eG : G ≃ G :=
    { toFun := fun g => ⟨u⁻¹ • (g : AdeleRing (𝓞 L) L), by
        obtain ⟨_, l, rfl⟩ := g
        exact ⟨(q⁻¹ : Lˣ) * l, by rw [map_mul]; rfl⟩⟩
      invFun := fun g => ⟨u • (g : AdeleRing (𝓞 L) L), by
        obtain ⟨_, l, rfl⟩ := g
        exact ⟨(q : L) * l, by rw [map_mul]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (smul_inv_smul u (g : AdeleRing (𝓞 L) L))
      right_inv := fun g => Subtype.ext (inv_smul_smul u (g : AdeleRing (𝓞 L) L)) }
  have hB' : IsAddFundamentalDomain G (e '' adelicBox L) μ := by
    refine hB.image_of_equiv e.toEquiv ((hmpe.symm e).quasiMeasurePreserving) eG fun g x => ?_
    show u • ((u⁻¹ • (g : AdeleRing (𝓞 L) L)) + x) = (g : AdeleRing (𝓞 L) L) + u • x
    rw [smul_add, smul_inv_smul]
  haveI : Countable L := countable_numberField L
  haveI : Countable G := by
    have hc : (G : Set (AdeleRing (𝓞 L) L)).Countable := by
      rw [hG]; exact Set.countable_range (algebraMap L (AdeleRing (𝓞 L) L))
    exact hc.to_subtype
  refine hB'.setIntegral_eq hB fun g x => ?_
  obtain ⟨_, l, rfl⟩ := g
  exact hper l x

end Box

section FibreKernels

open AutomorphicForm AutomorphicForm.TwistedBruhat NumberField.AdelicHeight IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicBox

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] borelSpace_adele

def Bf (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ T, φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)

def CTf (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) : ℂ :=
  constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) (fun t => unipotentGL2 t)
    (Bf K L D σ T φ x) y

variable {K L D σ}

theorem Bf_globalPoints_mul {T T' : Set (GL (Fin 2) L)} (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hbij : Set.BijOn (fun δ : GL (Fin 2) L => h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) T T')
    (x y : AdelicGL2 (𝓞 L) L) :
    Bf K L D σ T φ (globalPoints (𝓞 L) L h * x) y = Bf K L D σ T' φ x ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  unfold Bf
  exact finsum_mem_eq_of_bijOn _ hbij fun δ _ => congrArg φ (conj_identity K L D σ h δ x y)

theorem Bf_fib_unipotent_mul (p q : L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) (l : L) :
    Bf K L D σ (fib L p q) φ x (globalPoints (𝓞 L) L (unipotentGL2 l) * y) = Bf K L D σ (fib L p q) φ x y := by
  unfold Bf
  have hm : Matrix.GeneralLinearGroup.map (σ : L →+* L) (unipotentGL2 l) = unipotentGL2 ((σ : L →+* L) l) :=
    map_unipotentGL2 _ l
  have hm0 : ((unipotentGL2 ((σ : L →+* L) l) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    simp [unipotentGL2_coe]
  have hm1 : ((unipotentGL2 ((σ : L →+* L) l) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
    simp [unipotentGL2_coe]
  have hm2 : ((unipotentGL2 ((σ : L →+* L) l) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    simp [unipotentGL2_coe]
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_fib_of_unipotent p q hm0 hm1 hm2) fun δ _ => ?_
  rw [map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints', hm, map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

theorem CTf_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (p q p' q' : L)
    (hp' : p' = p * (σ ((h : Matrix (Fin 2) (Fin 2) L) 1 1) / (h : Matrix (Fin 2) (Fin 2) L) 1 1))
    (hq' : q' = q * (σ ((h : Matrix (Fin 2) (Fin 2) L) 0 0) / (h : Matrix (Fin 2) (Fin 2) L) 0 0))
    (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    CTf K L D σ (fib L p q) φ (globalPoints (𝓞 L) L h * x)
        (centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L h * x)) =
      CTf K L D σ (fib L p' q') φ x (centralScalar (𝓞 L) L z * x) := by
  have h00 : (h : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := apply_zero_zero_ne_zero_of_upper hh
  have h11 : (h : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := apply_one_one_ne_zero_of_upper hh
  have hbij := bijOn_twistedConj_fib (σ : L →+* L) hh p q p' q' hp' hq'
  set lam : Lˣ := Units.mk0 ((h : Matrix (Fin 2) (Fin 2) L) 1 1 / (h : Matrix (Fin 2) (Fin 2) L) 0 0)
    (div_ne_zero h11 h00) with hlam
  unfold CTf constantTerm constantTermIntegrand
  have hpt : ∀ t : AdeleRing (𝓞 L) L,
      Bf K L D σ (fib L p q) φ (globalPoints (𝓞 L) L h * x)
          (unipotentGL2 t * (centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L h * x))) =
        Bf K L D σ (fib L p' q') φ x
          (unipotentGL2 ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) lam) • t) *
            (centralScalar (𝓞 L) L z * x)) := by
    intro t
    rw [Bf_globalPoints_mul φ hbij, ← mul_cs_left, ← mul_assoc (unipotentGL2 t),
      unipotentGL2_mul_globalPoints L hh, mul_assoc, inv_mul_cancel_left]
    rfl
  simp_rw [hpt]
  refine integral_cond_adelicBox_comp_smul L
    (fun t => Bf K L D σ (fib L p' q') φ x (unipotentGL2 t * (centralScalar (𝓞 L) L z * x))) (fun l t => ?_) lam
  show Bf K L D σ (fib L p' q') φ x
      (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l + t) * (centralScalar (𝓞 L) L z * x)) = _
  rw [unipotentGL2_add, ← globalPoints_unipotentGL2, mul_assoc, Bf_fib_unipotent_mul]

end FibreKernels

section IndexEquiv

open AutomorphicForm AutomorphicForm.TwistedBruhat NumberField.AdelicHeight IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicBox

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

abbrev N1 : Type := {a : Lˣ // Algebra.norm K (a : L) = 1}

variable {K L}

def mulN1 (w : Lˣ) (hw : Algebra.norm K (w : L) = 1) : N1 K L ≃ N1 K L where
  toFun a := ⟨a.1 * w, by rw [Units.val_mul, map_mul, a.2, hw, one_mul]⟩
  invFun a := ⟨a.1 * w⁻¹, by
    rw [Units.val_mul, map_mul, a.2, one_mul, Units.val_inv_eq_inv_val, norm_inv' (Units.ne_zero w), hw,
      inv_one]⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

@[scoped simp] theorem mulN1_apply_val (w : Lˣ) (hw : Algebra.norm K (w : L) = 1) (a : N1 K L) :
    ((mulN1 w hw a).1 : Lˣ) = a.1 * w := rfl

theorem norm_sigma_div (σ : L ≃ₐ[K] L) {x : L} (hx : x ≠ 0) : Algebra.norm K (σ x / x) = 1 := by
  rw [div_eq_mul_inv, map_mul, norm_inv' hx, Algebra.norm_eq_of_algEquiv,
    mul_inv_cancel₀ (Algebra.norm_ne_zero_iff.mpr hx)]

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adele

variable (K L) in

def fibreTerm (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (g : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : ℂ :=
  (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
      φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@AutomorphicForm.constantTerm _
      (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
          (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
          (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ y)))
      (AutomorphicForm.centralScalar (𝓞 L) L z * g)

theorem fibreTerm_eq (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (g : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (s : Lˣ) (a : N1 K L) :
    fibreTerm K L D σ hgen φ R g z s a =
      Bf K L D σ (normUnipotentSet K L σ hgen ∩ fib L (s : L) ((s : L) * ((a : Lˣ) : L))) φ g
          (centralScalar (𝓞 L) L z * g) -
        Set.indicator (highSet (adelicHeight L) (Real.exp R))
          (CTf K L D σ (fib L (s : L) ((s : L) * ((a : Lˣ) : L))) φ g) (centralScalar (𝓞 L) L z * g) :=
  rfl

theorem fibreTerm_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) {b : GL (Fin 2) L}
    (hb : b ∈ borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) (s : Lˣ) (a : N1 K L)
    (u₁ u₀ : Lˣ) (hu₁ : (u₁ : L) = σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1)
    (hu₀ : (u₀ : L) = σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0)
    (hw : Algebra.norm K ((u₀ * u₁⁻¹ : Lˣ) : L) = 1) :
    fibreTerm K L D σ hgen φ R (globalPoints (𝓞 L) L b * g) z s a =
      fibreTerm K L D σ hgen φ R g z (s * u₁) (mulN1 (u₀ * u₁⁻¹) hw a) := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hb

  set p' : L := ((s * u₁ : Lˣ) : L) with hp'def
  set q' : L := ((s * u₁ : Lˣ) : L) * (((mulN1 (u₀ * u₁⁻¹) hw a).1 : Lˣ) : L) with hq'def
  have hp' : p' = (s : L) * (σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [hp'def, Units.val_mul, hu₁]
  have hq' : q' = (s : L) * ((a : Lˣ) : L) *
      (σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    have hu₁0 : (u₁ : L) ≠ 0 := Units.ne_zero u₁
    rw [hq'def, mulN1_apply_val, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, ← hu₀]
    field_simp
  have hbijT : Set.BijOn (fun δ : GL (Fin 2) L => b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b)
      (fib L (s : L) ((s : L) * ((a : Lˣ) : L))) (fib L p' q') :=
    bijOn_twistedConj_fib (σ : L →+* L) hb' _ _ p' q' hp' hq'
  have hbijK : Set.BijOn (fun δ : GL (Fin 2) L => b⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b)
      (normUnipotentSet K L σ hgen ∩ fib L (s : L) ((s : L) * ((a : Lˣ) : L)))
      (normUnipotentSet K L σ hgen ∩ fib L p' q') := by
    refine (bijOn_twistedConj_normUnipotentSet hgen b).inter hbijT fun δ _ δ' _ hh => ?_
    have := congrArg (fun y => b * y * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹) hh
    simpa [mul_assoc] using this
  rw [fibreTerm_eq, fibreTerm_eq]
  congr 1
  ·
    rw [← mul_cs_left, Bf_globalPoints_mul φ hbijK, inv_mul_cancel_left]
  ·
    have hmem : centralScalar (𝓞 L) L z * (globalPoints (𝓞 L) L b * g) ∈ highSet (adelicHeight L) (Real.exp R) ↔
        centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R) := by
      rw [mem_highSet_iff, mem_highSet_iff, ← mul_cs_left,
        NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (γ := b) hb]
    by_cases hx : centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx),
        CTf_globalPoints_mul φ hb' _ _ p' q' hp' hq']
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

theorem tsum_enorm_fibreTerm_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) {b : GL (Fin 2) L}
    (hb : b ∈ borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
        ‖fibreTerm K L D σ hgen φ R (globalPoints (𝓞 L) L b * g) z s a‖ₑ) =
      ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1}, ‖fibreTerm K L D σ hgen φ R g z s a‖ₑ := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hb
  have h11 : (b : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := apply_one_one_ne_zero_of_upper hb'
  have h00 : (b : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := apply_zero_zero_ne_zero_of_upper hb'
  have hσ11 : σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).mpr h11
  have hσ00 : σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := (map_ne_zero σ).mpr h00
  set u₁ : Lˣ := Units.mk0 (σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1)
    (div_ne_zero hσ11 h11) with hu₁
  set u₀ : Lˣ := Units.mk0 (σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0)
    (div_ne_zero hσ00 h00) with hu₀
  have hu₁v : (u₁ : L) = σ ((b : Matrix (Fin 2) (Fin 2) L) 1 1) / (b : Matrix (Fin 2) (Fin 2) L) 1 1 := rfl
  have hu₀v : (u₀ : L) = σ ((b : Matrix (Fin 2) (Fin 2) L) 0 0) / (b : Matrix (Fin 2) (Fin 2) L) 0 0 := rfl
  have hw : Algebra.norm K ((u₀ * u₁⁻¹ : Lˣ) : L) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, norm_inv' (Units.ne_zero u₁), hu₁v, hu₀v,
      norm_sigma_div σ h11, norm_sigma_div σ h00, inv_one, mul_one]
  let e : Lˣ × N1 K L ≃ Lˣ × N1 K L := Equiv.prodCongr (Equiv.mulRight u₁) (mulN1 (u₀ * u₁⁻¹) hw)
  rw [← ENNReal.tsum_prod, ← ENNReal.tsum_prod]
  have key : ∀ x : Lˣ × N1 K L,
      ‖fibreTerm K L D σ hgen φ R (globalPoints (𝓞 L) L b * g) z x.1 x.2‖ₑ =
        (fun y : Lˣ × N1 K L => ‖fibreTerm K L D σ hgen φ R g z y.1 y.2‖ₑ) (e x) := by
    intro x
    rw [fibreTerm_globalPoints_mul D σ hgen φ R hb g z x.1 x.2 u₁ u₀ hu₁v hu₀v hw]
    rfl
  rw [tsum_congr key]
  exact Equiv.tsum_eq e (fun y : Lˣ × N1 K L => ‖fibreTerm K L D σ hgen φ R g z y.1 y.2‖ₑ)

variable (K L) in

def fibreFold {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
    ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
      ‖fibreTerm K L D σ hgen φ R g z s a‖ₑ ∂νZL

theorem fibreFold_globalPoints_mul {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) {b : GL (Fin 2) L} (hb : b ∈ borelSubgroup L) (g : AdelicGL2 (𝓞 L) L) :
    fibreFold K L D σ hgen νZL ΩL ξL φ R (globalPoints (𝓞 L) L b * g) = fibreFold K L D σ hgen νZL ΩL ξL φ R g := by
  unfold fibreFold
  refine lintegral_congr fun z => ?_
  rw [tsum_enorm_fibreTerm_globalPoints_mul D σ hgen φ R hb g z]

end IndexEquiv

section Continuity

open AutomorphicForm IsDedekindDomain

variable (L : Type) [Field L] [NumberField L]

theorem countable_gl : Countable (GL (Fin 2) L) := by
  haveI : Countable L := Function.Injective.countable (Module.finBasis ℚ L).equivFun.injective
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Units.val_injective.countable

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := countable_numberField L
  exact Units.val_injective.countable

theorem exists_finite_forall_ne_zero_mem (hfin : AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹}, hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : globalPoints (𝓞 L) L δ = x * (x⁻¹ * globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

theorem finsum_mem_eq_sum_of_mem (hfin : AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ t : Finset (GL (Fin 2) L), (t : Set (GL (Fin 2) L)) ⊆ T ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) = ∑ δ ∈ t, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  refine ⟨hΓT.toFinset, fun δ hδ => (hΓT.mem_toFinset.mp hδ).2, fun x hx y hy => ?_⟩
  apply finsum_mem_eq_sum_of_subset
  · rintro δ ⟨hδT, hδs⟩
    exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
  · intro δ hδ
    exact (hΓT.mem_toFinset.mp hδ).2

theorem continuous_finsum_mem (hfin : AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (p.1⁻¹ * globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨t, -, ht⟩ := finsum_mem_eq_sum_of_mem L hfin φ hφs T hX hY
  have hsum : Continuous fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ t, φ (q.1⁻¹ * globalPoints (𝓞 L) L δ * q.2) := by
    refine continuous_finsetSum t fun δ _ => hφc.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul continuous_snd
  refine ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt ?_
  exact prod_mem_nhds hXn hYn

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_val
    · exact continuous_const
  · refine continuous_matrix fun i j => ?_
    change Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_coe_inv
    · exact continuous_const

theorem secondCountableTopology_units_adeleRing : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end Continuity

section Measurability

open AutomorphicForm AutomorphicForm.TwistedBruhat NumberField.AdelicHeight IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicBox

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adele

theorem continuous_comp_pair {X W P : Type} [TopologicalSpace X] [TopologicalSpace W] [TopologicalSpace P]
    (F : X → W → ℂ) (hF : Continuous fun q : X × W => F q.1 q.2) (a : P → X) (ha : Continuous a) (e : P → W)
    (he : Continuous e) : Continuous fun p : P => F (a p) (e p) :=
  hF.comp (ha.prodMk he)

theorem continuous_unipotentGL2' :
    Continuous fun q : AdeleRing (𝓞 L) L => (unipotentGL2 q : AdelicGL2 (𝓞 L) L) :=
  AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)

theorem continuous_Bf (hloc : AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Bf K L D σ T' φ p.1 (centralScalar (𝓞 L) L p.2 * p.1) := by
  unfold Bf
  exact continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') Prod.fst continuous_fst
    (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1))
    ((continuous_sigmaAdelicAct K L D σ).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem continuous_Bf_unipotent (hloc : AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      Bf K L D σ T' φ r.1.1 (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)) := by
  unfold Bf
  refine continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T')
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L => r.1.1)
    (continuous_fst.comp continuous_fst)
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      sigmaAdelicAct K L D σ (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) ?_
  exact (continuous_sigmaAdelicAct K L D σ).comp
    (((continuous_unipotentGL2' L).comp continuous_snd).mul
      ((((continuous_centralScalar L).comp (continuous_snd.comp continuous_fst))).mul
        (continuous_fst.comp continuous_fst)))

open Classical in

theorem indicator_CTf_eq_ite (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (T' : Set (GL (Fin 2) L))
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Set.indicator (highSet (adelicHeight L) (Real.exp R)) (CTf K L D σ T' φ g) (centralScalar (𝓞 L) L z * g) =
      if Real.exp R < adelicHeight L (centralScalar (𝓞 L) L z * g) then
        ∫ q, Bf K L D σ T' φ g (unipotentGL2 q * (centralScalar (𝓞 L) L z * g))
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
      else 0 := by
  rw [Set.indicator_apply]
  rfl

theorem measurable_fibreTerm
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (hloc : AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (s : Lˣ) (a : N1 K L) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => fibreTerm K L D σ hgen φ R p.1 p.2 s a := by
  classical
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_units_adeleRing L
  simp only [fibreTerm_eq]
  set T' : Set (GL (Fin 2) L) := normUnipotentSet K L σ hgen ∩ fib L (s : L) ((s : L) * ((a : Lˣ) : L))
  set T'' : Set (GL (Fin 2) L) := fib L (s : L) ((s : L) * ((a : Lˣ) : L))
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Bf K L D σ T' φ p.1 (centralScalar (𝓞 L) L p.2 * p.1) :=
    (continuous_Bf K L D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < adelicHeight L (centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        Bf K L D σ T'' φ r.1.1 (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) (p, q)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_Bf_unipotent K L D σ hloc φ hφc hφs T'').stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Set.indicator (highSet (adelicHeight L) (Real.exp R)) (CTf K L D σ T'' φ p.1)
        (centralScalar (𝓞 L) L p.2 * p.1) := by
    simp_rw [indicator_CTf_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hKm.sub hTm

theorem measurable_fibreFold
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hloc : AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) :
    Measurable (fibreFold K L D σ hgen νZL ΩL ξL φ R) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_units_adeleRing L
  haveI : SigmaFinite νZL := inferInstance
  haveI : Countable Lˣ := countable_units L
  have hξm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) :=
    hξc.measurable.comp measurable_snd
  have hH : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ)‖ₑ *
        ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
          ‖fibreTerm K L D σ hgen φ R p.1 p.2 s a‖ₑ := by
    refine hξm.enorm.mul ?_
    refine Measurable.ennreal_tsum fun s => ?_
    refine Measurable.ennreal_tsum fun a => ?_
    exact (measurable_fibreTerm K L D σ hgen hloc φ hφc hφs R s a).enorm
  unfold fibreFold
  exact hH.lintegral_prod_right' (ν := νZL.restrict ΩL)

end Measurability

section Shell

open AutomorphicForm NumberField.TateGlobal IsDedekindDomain NumberField.AdelicHaar

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adele

theorem borelSpace_GL2 : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_GL2

theorem measurableSet_detShell (α β : ℝ) :
    MeasurableSet {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc

theorem det_globalPoints (γ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem ideleNorm_principal (q : Lˣ) :
    ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom q) = 1 := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_algebraMap L q]
  simp

theorem globalPoints_mul_mem_detShell_iff (α β : ℝ) (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * g ∈ {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ↔
      g ∈ {g : AdelicGL2 (𝓞 L) L | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, map_mul, ideleNorm_mul, det_globalPoints, ideleNorm_principal, one_mul]

theorem ne_top_of_eq_mul {a b c : ℝ≥0∞} (h : a = c * b) (ha : a ≠ ⊤) (hc : c ≠ 0) : b ≠ ⊤ := by
  intro hb
  rw [hb, ENNReal.mul_top hc] at h
  exact ha h

end Shell

end R1FibreUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

open R1FibreUnfold
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm
open IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace G4B1
open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm in
theorem fibreTerm_one_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (g : AdelicGL2 (𝓞 L) L)
    (ζ : (AdeleRing (𝓞 L) L)ˣ) (a : R1FibreUnfold.N1 K L) :
    R1FibreUnfold.fibreTerm K L D σ hgen φ R g ζ 1 a =
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * g) := by
  simp only [R1FibreUnfold.fibreTerm, Units.val_one, one_mul]
end G4B1
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain
open scoped ENNReal NNReal

noncomputable section

namespace TorusUnfold

section Pieces

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_idele' : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem sigmaFinite_idelicHaar' : SigmaFinite (NumberField.Idele.idelicHaar L) := by
  haveI := secondCountableTopology_idele' L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

theorem setIntegral2_congr_of_lintegral_ne_top
    (V V' : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (Φ : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞)
    (hΦ : Measurable (Function.uncurry Φ)) (hV : ∀ x t, Φ x t ≠ ⊤ → V x t = V' x t)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω, Φ x t ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    ∫ x in X, ∫ t in Ω, V x t ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω, V' x t ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) := by
  haveI := sigmaFinite_idelicHaar' L
  have hm : Measurable fun x : AdeleRing (𝓞 L) L => ∫⁻ t in Ω, Φ x t ∂(NumberField.Idele.idelicHaar L) :=
    hΦ.lintegral_prod_right'
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hm hfin] with x hx
  have hmx : Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => Φ x t := hΦ.comp (measurable_const.prodMk measurable_id)
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hmx hx.ne] with t ht
  exact hV x t ht.ne

theorem continuous_diagOne' :
    Continuous (fun t : (AdeleRing (𝓞 L) L)ˣ => (diagOne t : AdelicGL2 (𝓞 L) L)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 L) L), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => (t : AdeleRing (𝓞 L) L)
      exact Units.continuous_val
    · exact continuous_const
  · simp_rw [← map_inv]
    show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
      exact Units.continuous_coe_inv
    · exact continuous_const

theorem continuous_word :
    Continuous fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) =>
      unipotentGL2 p.1 * (diagOne p.2.1 : AdelicGL2 (𝓞 L) L) * (p.2.2 : AdelicGL2 (𝓞 L) L) :=
  (((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).comp continuous_fst).mul
    ((continuous_diagOne' L).comp continuous_snd.fst)).mul (continuous_subtype_val.comp continuous_snd.snd)

theorem measurable_kfold (Z : AdelicGL2 (𝓞 L) L → ℂ) (hZ : Measurable Z) :
    Measurable (Function.uncurry fun (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) =>
      ∫ k, Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
        (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ) ∂(maximalCompactHaar L)) := by
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI := secondCountableTopology_idele' L
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  have hw : Measurable fun q : (AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × ↥(adelicMaximalCompact L) =>
      Z (unipotentGL2 q.1.1 * diagOne q.1.2 * (q.2 : AdelicGL2 (𝓞 L) L)) *
        (((NumberField.TateGlobal.ideleNorm L q.1.2)⁻¹ : ℝ) : ℂ) := by
    refine Measurable.mul ?_ ?_
    · exact hZ.comp ((continuous_word L).comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).measurable
    · exact (Complex.continuous_ofReal.measurable.comp
        (((NumberField.TateGlobal.continuous_ideleNorm L).measurable.comp measurable_fst.snd).inv))
  exact (hw.stronglyMeasurable.integral_prod_right' (ν := maximalCompactHaar L)).measurable

theorem measurable_kfold_lintegral (Z : AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hZ : Measurable Z) :
    Measurable (Function.uncurry fun (x : AdeleRing (𝓞 L) L) (t : (AdeleRing (𝓞 L) L)ˣ) =>
      ∫⁻ k, Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹ ∂(maximalCompactHaar L)) := by
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI := secondCountableTopology_idele' L
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  have hw : Measurable fun q : (AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × ↥(adelicMaximalCompact L) =>
      Z (unipotentGL2 q.1.1 * diagOne q.1.2 * (q.2 : AdelicGL2 (𝓞 L) L)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L q.1.2)⁻¹ := by
    refine Measurable.mul ?_ ?_
    · exact hZ.comp ((continuous_word L).comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).measurable
    · exact ENNReal.measurable_ofReal.comp
        (((NumberField.TateGlobal.continuous_ideleNorm L).measurable.comp measurable_fst.snd).inv)
  exact hw.lintegral_prod_right'

end Pieces
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

section Parametric

theorem measurable_integral_of_uncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] (f : α → β → ℂ) (hf : Measurable (Function.uncurry f)) :
    Measurable fun a => ∫ b, f a b ∂ν :=
  (hf.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem measurable_lintegral_of_uncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] (F : α → β → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    Measurable fun a => ∫⁻ b, F a b ∂ν :=
  hF.lintegral_prod_right'

theorem measurable_lintegral_tsum_of_uncurry {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable ι] (ν : Measure β) [SFinite ν] (w : β → ℝ≥0∞) (hw : Measurable w)
    (F : ι → α → β → ℝ≥0∞) (hF : ∀ i, Measurable (Function.uncurry (F i))) :
    Measurable fun a => ∫⁻ b, w b * ∑' i, F i a b ∂ν := by
  have h : Measurable fun p : α × β => w p.2 * ∑' i, F i p.1 p.2 :=
    (hw.comp measurable_snd).mul (Measurable.ennreal_tsum fun i => hF i)
  exact h.lintegral_prod_right'

end Parametric
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

end TorusUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

end
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace TorusUnfold

section Fubini4

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (L : Type) [Field L] [NumberField L]

theorem integral4_move_x_inside (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [SFinite ν]
    (X : Set (AdeleRing (𝓞 L) L)) (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (F : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hF : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
        (AdeleRing (𝓞 L) L)ˣ => F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, (∫⁻ ζ, ‖F x t k ζ‖ₑ ∂ν) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    ∫ x in X, ∫ t in Ω, ∫ k, (∫ ζ, F x t k ζ ∂ν) * (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) =
      ∫ t in Ω, ∫ k, (∫ ζ, (∫ x in X, F x t k ζ ∂(adelicAddHaar (𝓞 L) L)) ∂ν) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) := by
  haveI : SigmaFinite (NumberField.Idele.idelicHaar L) := sigmaFinite_idelicHaar' L
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI : SigmaFinite (adelicAddHaar (𝓞 L) L) := by unfold adelicAddHaar; infer_instance
  set μX : Measure (AdeleRing (𝓞 L) L) := (adelicAddHaar (𝓞 L) L).restrict X with hμX
  set μT : Measure (AdeleRing (𝓞 L) L)ˣ := (NumberField.Idele.idelicHaar L).restrict Ω with hμT
  set μk : Measure ↥(adelicMaximalCompact L) := maximalCompactHaar L with hμk
  set c : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun t => (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ) with hc
  have hcm : Measurable c :=
    Complex.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L).measurable.inv
  have hce : ∀ t, ‖c t‖ₑ = ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹ := by
    intro t
    have h0 : 0 ≤ (NumberField.TateGlobal.ideleNorm L t)⁻¹ :=
      inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos t).le
    rw [hc, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

  set Φ : AdeleRing (𝓞 L) L × ((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) → ℂ :=
    fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2 * c p.2.1 with hΦ
  have hΦm : Measurable Φ := hF.mul (hcm.comp (measurable_fst.comp measurable_snd))

  have hΦi : Integrable Φ (μX.prod (μT.prod (μk.prod ν))) := by
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Φ p‖ₑ ∂(μX.prod (μT.prod (μk.prod ν))) < ⊤
    rw [lintegral_prod _ hΦm.enorm.aemeasurable]
    have e1 : ∀ x, ∫⁻ q, ‖Φ (x, q)‖ₑ ∂(μT.prod (μk.prod ν)) =
        ∫⁻ t, ∫⁻ k, (∫⁻ ζ, ‖F x t k ζ‖ₑ ∂ν) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹ ∂μk ∂μT := by
      intro x
      have hmx : Measurable fun q : (AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ) =>
          ‖Φ (x, q)‖ₑ := (hΦm.comp (measurable_const.prodMk measurable_id)).enorm
      rw [lintegral_prod _ hmx.aemeasurable]
      refine lintegral_congr fun t => ?_
      have hmxt : Measurable fun q : ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ => ‖Φ (x, (t, q))‖ₑ :=
        hmx.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hmxt.aemeasurable]
      refine lintegral_congr fun k => ?_
      show ∫⁻ ζ, ‖F x t k ζ * c t‖ₑ ∂ν = _
      simp_rw [enorm_mul, hce]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    simp_rw [e1]
    exact lt_top_iff_ne_top.2 hfin

  have lhs1 : ∀ x, (∫ t, ∫ k, (∫ ζ, F x t k ζ ∂ν) * c t ∂μk ∂μT) =
      ∫ t, ∫ k, ∫ ζ, Φ (x, (t, (k, ζ))) ∂ν ∂μk ∂μT := by
    intro x
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show (∫ ζ, F x t k ζ ∂ν) * c t = ∫ ζ, F x t k ζ * c t ∂ν
    exact (integral_mul_const (c t) _).symm
  have lhs2 : ∀ᵐ x ∂μX, (∫ t, ∫ k, ∫ ζ, Φ (x, (t, (k, ζ))) ∂ν ∂μk ∂μT) =
      ∫ q, Φ (x, q) ∂(μT.prod (μk.prod ν)) := by
    filter_upwards [hΦi.prod_right_ae] with x hx
    rw [integral_prod _ hx]
    refine integral_congr_ae ?_
    filter_upwards [hx.prod_right_ae] with t ht
    rw [integral_prod _ ht]

  have hI : Integrable (fun q : (AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ) =>
      ∫ x, Φ (x, q) ∂μX) (μT.prod (μk.prod ν)) := hΦi.integral_prod_right
  have rhs1 : (∫ q, ∫ x, Φ (x, q) ∂μX ∂(μT.prod (μk.prod ν))) =
      ∫ t, ∫ k, ∫ ζ, ∫ x, Φ (x, (t, (k, ζ))) ∂μX ∂ν ∂μk ∂μT := by
    rw [integral_prod _ hI]
    refine integral_congr_ae ?_
    filter_upwards [hI.prod_right_ae] with t ht
    rw [integral_prod _ ht]
  have rhs2 : ∀ t k, (∫ ζ, ∫ x, Φ (x, (t, (k, ζ))) ∂μX ∂ν) = (∫ ζ, (∫ x, F x t k ζ ∂μX) ∂ν) * c t := by
    intro t k
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show ∫ x, F x t k ζ * c t ∂μX = (∫ x, F x t k ζ ∂μX) * c t
    exact integral_mul_const (c t) _

  calc (∫ x in X, ∫ t in Ω, ∫ k, (∫ ζ, F x t k ζ ∂ν) * c t ∂μk ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L))
      = ∫ x, ∫ q, Φ (x, q) ∂(μT.prod (μk.prod ν)) ∂μX := by
        refine integral_congr_ae ?_
        filter_upwards [lhs2] with x hx
        exact (lhs1 x).trans hx
    _ = ∫ p, Φ p ∂(μX.prod (μT.prod (μk.prod ν))) := (integral_prod _ hΦi).symm
    _ = ∫ q, ∫ x, Φ (x, q) ∂μX ∂(μT.prod (μk.prod ν)) := integral_prod_symm _ hΦi
    _ = ∫ t, ∫ k, ∫ ζ, ∫ x, Φ (x, (t, (k, ζ))) ∂μX ∂ν ∂μk ∂μT := rhs1
    _ = ∫ t in Ω, ∫ k, (∫ ζ, (∫ x in X, F x t k ζ ∂(adelicAddHaar (𝓞 L) L)) ∂ν) * c t ∂μk
          ∂(NumberField.Idele.idelicHaar L) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        exact rhs2 t k

end Fubini4
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

end TorusUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

namespace TorusUnfold

section Fubini4w

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (L : Type) [Field L] [NumberField L]

theorem integral4_move_x_inside' (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [SFinite ν]
    (X : Set (AdeleRing (𝓞 L) L)) (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (w : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hw : Measurable w)
    (F : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hF : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
        (AdeleRing (𝓞 L) L)ˣ => F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, (∫⁻ ζ, ‖w ζ‖ₑ * ‖F x t k ζ‖ₑ ∂ν) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    ∫ x in X, ∫ t in Ω, ∫ k, (∫ ζ, w ζ * F x t k ζ ∂ν) * (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) =
      ∫ t in Ω, ∫ k, (∫ ζ, w ζ * (∫ x in X, F x t k ζ ∂(adelicAddHaar (𝓞 L) L)) ∂ν) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) := by
  have h := integral4_move_x_inside L ν X Ω (fun x t k ζ => w ζ * F x t k ζ)
    ((hw.comp measurable_snd.snd.snd).mul hF) (by simp_rw [enorm_mul]; exact hfin)
  simp_rw [integral_const_mul] at h
  exact h

end Fubini4w
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

end TorusUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace G4B3ConjI

theorem lintegral3_ne_top_of_core (L : Type) [Field L] [NumberField L]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [SFinite ν]
    (X : Set (AdeleRing (𝓞 L) L)) (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (Φ : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞) (hΦ : Measurable Φ)
    (S : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hS : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
      (AdeleRing (𝓞 L) L)ˣ => S p.1 p.2.1 p.2.2.1 p.2.2.2)
    (B : (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hcore : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) (ζ : (AdeleRing (𝓞 L) L)ˣ),
      (c.toReal : ℂ) * B t k ζ = ∫ x in X, S x t k ζ ∂(adelicAddHaar (𝓞 L) L))
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, (∫⁻ ζ, Φ ζ * ‖S x t k ζ‖ₑ ∂ν) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
      ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    ∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, Φ ζ * ‖B t k ζ‖ₑ * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
      ∂ν ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SigmaFinite (adelicAddHaar (𝓞 L) L) := by unfold adelicAddHaar; infer_instance
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  haveI : SigmaFinite (NumberField.Idele.idelicHaar L) := by
    haveI := NumberField.Idele.isHaarMeasure_idelicHaar L
    infer_instance
  set μ := adelicAddHaar (𝓞 L) L with hμ
  set κ := maximalCompactHaar L with hκ
  set ρ := NumberField.Idele.idelicHaar L with hρ
  set w : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun t => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹ with hw
  have hwm : Measurable w :=
    ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L).measurable.inv

  have hB : ∀ t k ζ, ‖B t k ζ‖ₑ ≤ c⁻¹ * ∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ := by
    intro t k ζ
    have h1 : ‖(c.toReal : ℂ) * B t k ζ‖ₑ ≤ ∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ := by
      rw [hcore]; exact enorm_integral_le_lintegral_enorm _
    have h2 : ‖(c.toReal : ℂ) * B t k ζ‖ₑ = c * ‖B t k ζ‖ₑ := by
      rw [enorm_mul]
      congr 1
      rw [show ((c.toReal : ℝ) : ℂ) = ((c.toReal : ℝ) : ℂ) from rfl, ← ofReal_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcT]
    calc ‖B t k ζ‖ₑ = c⁻¹ * (c * ‖B t k ζ‖ₑ) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
      _ ≤ c⁻¹ * ∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ := mul_le_mul_right (h2 ▸ h1) _

  set H : AdeleRing (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ :=
    fun x t k ζ => Φ ζ * ‖S x t k ζ‖ₑ * w t with hH
  have hHm : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
      (AdeleRing (𝓞 L) L)ˣ => H p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp only [hH]
    exact ((hΦ.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul hS.enorm).mul
      (hwm.comp (measurable_fst.comp measurable_snd))
  have hw_ne : ∀ t, w t ≠ ⊤ := fun t => ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0

  have m1 : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)),
      Measurable fun q : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L => H q.2 t k q.1 := fun t k =>
    hHm.comp (measurable_snd.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_fst)))
  have m2 : ∀ (t : (AdeleRing (𝓞 L) L)ˣ),
      Measurable fun q : ↥(adelicMaximalCompact L) × AdeleRing (𝓞 L) L => ∫⁻ ζ, H q.2 t q.1 ζ ∂ν := by
    intro t
    have h : Measurable fun p : (↥(adelicMaximalCompact L) × AdeleRing (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ =>
        H p.1.2 t p.1.1 p.2 :=
      hHm.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_const.prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    exact h.lintegral_prod_right'
  have m3 : Measurable fun q : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L => ∫⁻ k, ∫⁻ ζ, H q.2 q.1 k ζ ∂ν ∂κ := by
    have h : Measurable fun p : (((AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L) × ↥(adelicMaximalCompact L)) ×
        (AdeleRing (𝓞 L) L)ˣ => H p.1.1.2 p.1.1.1 p.1.2 p.2 :=
      hHm.comp (((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk
        (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    exact (h.lintegral_prod_right').lintegral_prod_right'
  have mx : ∀ t k ζ, Measurable fun x : AdeleRing (𝓞 L) L => ‖S x t k ζ‖ₑ := fun t k ζ =>
    (hS.comp (measurable_id.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_const)))).enorm

  have hle : (∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, Φ ζ * ‖B t k ζ‖ₑ * w t ∂ν ∂κ ∂ρ) ≤
      ∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, c⁻¹ * ∫⁻ x in X, H x t k ζ ∂μ ∂ν ∂κ ∂ρ := by
    refine lintegral_mono fun t => lintegral_mono fun k => lintegral_mono fun ζ => ?_
    have hI : (∫⁻ x in X, H x t k ζ ∂μ) = Φ ζ * (∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ) * w t := by
      simp only [hH]
      rw [lintegral_mul_const _ ((mx t k ζ).const_mul _), lintegral_const_mul _ (mx t k ζ)]
    rw [hI, show c⁻¹ * (Φ ζ * (∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ) * w t) =
      Φ ζ * (c⁻¹ * ∫⁻ x in X, ‖S x t k ζ‖ₑ ∂μ) * w t by ring]
    exact mul_le_mul_left (mul_le_mul_right (hB t k ζ) _) _

  have hswap : (∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, ∫⁻ x in X, H x t k ζ ∂μ ∂ν ∂κ ∂ρ) =
      ∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, H x t k ζ ∂ν ∂κ ∂ρ ∂μ := by
    have s1 : ∀ t k, (∫⁻ ζ, ∫⁻ x in X, H x t k ζ ∂μ ∂ν) = ∫⁻ x in X, ∫⁻ ζ, H x t k ζ ∂ν ∂μ := fun t k =>
      lintegral_lintegral_swap ((m1 t k).aemeasurable)
    simp_rw [s1]
    have s2 : ∀ t, (∫⁻ k, ∫⁻ x in X, ∫⁻ ζ, H x t k ζ ∂ν ∂μ ∂κ) = ∫⁻ x in X, ∫⁻ k, ∫⁻ ζ, H x t k ζ ∂ν ∂κ ∂μ :=
      fun t => lintegral_lintegral_swap ((m2 t).aemeasurable)
    simp_rw [s2]
    exact lintegral_lintegral_swap (m3.aemeasurable)
  have hfin' : (∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, H x t k ζ ∂ν ∂κ ∂ρ ∂μ) ≠ ⊤ := by
    have heq : (∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, ∫⁻ ζ, H x t k ζ ∂ν ∂κ ∂ρ ∂μ) =
        ∫⁻ x in X, ∫⁻ t in Ω, ∫⁻ k, (∫⁻ ζ, Φ ζ * ‖S x t k ζ‖ₑ ∂ν) * w t ∂κ ∂ρ ∂μ := by
      refine lintegral_congr fun x => lintegral_congr fun t => lintegral_congr fun k => ?_
      simp only [hH]
      rw [lintegral_mul_const' _ _ (hw_ne t)]
    rw [heq]; exact hfin
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_congr fun t => lintegral_congr fun k => lintegral_const_mul' c⁻¹ _ hcinv,
    lintegral_congr fun t => lintegral_const_mul' c⁻¹ _ hcinv, lintegral_const_mul' c⁻¹ _ hcinv, hswap]
  exact ENNReal.mul_ne_top hcinv hfin'

end G4B3ConjI
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace XMerge

theorem integrableOn_and_setIntegral_unitFibre_sub_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) :
    IntegrableOn (fun x : AdeleRing (𝓞 L) L =>
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))
      X (adelicAddHaar (𝓞 L) L) ∧
    (∫ x in X,
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) *
        ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
          (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
            ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) := by
  obtain ⟨hIK, hK⟩ :=
    AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
      K L D σ hgen φ hφc hφs X hX μK hμK1 c hc0 hcT hc t ζ k
  obtain ⟨hIT, hT⟩ :=
    AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward
      K L D σ φ hφc hφs R X hX μK hμK1 c hc0 hcT hc t ζ k
  have hX1 : ∀ x : AdeleRing (𝓞 L) L,
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ
                        (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) =
      ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k) := fun x =>
    (AutomorphicForm.TwistedBruhat.finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
      K L D σ hgen φ x 0 t ζ (k : AdelicGL2 (𝓞 L) L)).1
  have hIK' : IntegrableOn (fun x : AdeleRing (𝓞 L) L => (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ
                        (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))))) X (adelicAddHaar (𝓞 L) L) := by
    simp_rw [hX1]; exact hIK
  refine ⟨hIK'.sub hIT, ?_⟩
  rw [integral_sub hIK' hIT, hT, mul_sub]
  congr 1
  simp_rw [hX1]
  exact hK

end XMerge
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AutomorphicForm.AdelicTracePushforward AutomorphicForm.TwistedBruhat
open scoped TensorProduct Pointwise ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace XMergeAssembly

def one₁ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    R1FibreUnfold.N1 K L := ⟨1, by rw [Units.val_one, map_one]⟩

theorem one₁_val' (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ((((one₁ K L) : R1FibreUnfold.N1 K L).1 : Lˣ) : L) = 1 := rfl

theorem xmerge_main
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤)  :
   (∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) ∧
    (∫ x in X, ∫ t in Ω₂K, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      (c.toReal : ℂ) * ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)) := by
  have hm : ‹MeasurableSpace (AdeleRing (𝓞 L) L)ˣ› = NumberField.Idele.ideleBorel L := BorelSpace.measurable_eq
  subst hm
  have hloc : AdelicKernelLocalFiniteness L := AutomorphicForm.adelicKernelLocalFiniteness L
  haveI := TorusUnfold.secondCountableTopology_idele' L
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L

  have core := fun (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) =>
    XMerge.integrableOn_and_setIntegral_unitFibre_sub_eq K L D σ hgen φ hφc hφs R X hX μK hμK1 c hc0 hcT hc t ζ k

  have hw : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
      (AdeleRing (𝓞 L) L)ˣ =>
      ((unipotentGL2 p.1 * diagOne p.2.1 * (p.2.2.1 : AdelicGL2 (𝓞 L) L)), p.2.2.2) :=
    ((TorusUnfold.continuous_word L).measurable.comp
      (measurable_fst.prodMk ((measurable_snd.fst).prodMk measurable_snd.snd.fst))).prodMk
      measurable_snd.snd.snd
  have h1 : Measurable (fun q : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1FibreUnfold.fibreTerm K L D σ hgen φ R q.1 q.2 1 (one₁ K L)) :=
    R1FibreUnfold.measurable_fibreTerm K L D σ hgen hloc φ hφc hφs R 1 (one₁ K L)
  have hS0 : Measurable ((fun q : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1FibreUnfold.fibreTerm K L D σ hgen φ R q.1 q.2 1 (one₁ K L)) ∘
      (fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ =>
        ((unipotentGL2 p.1 * diagOne p.2.1 * (p.2.2.1 : AdelicGL2 (𝓞 L) L)), p.2.2.2))) := h1.comp hw
  have hSe : (fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
      (AdeleRing (𝓞 L) L)ˣ => (fun x t k ζ => (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) p.1 p.2.1 p.2.2.1 p.2.2.2) =
      ((fun q : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
        R1FibreUnfold.fibreTerm K L D σ hgen φ R q.1 q.2 1 (one₁ K L)) ∘
      (fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ =>
        ((unipotentGL2 p.1 * diagOne p.2.1 * (p.2.2.1 : AdelicGL2 (𝓞 L) L)), p.2.2.2))) := by
    funext p
    simp only [Function.comp_apply]
    rw [G4B1.fibreTerm_one_eq]
    rfl
  have hS : Measurable fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L) ×
      (AdeleRing (𝓞 L) L)ˣ => (fun x t k ζ => (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    rw [hSe]; exact hS0
  refine ⟨?_, ?_⟩
  ·
    exact G4B3ConjI.lintegral3_ne_top_of_core L νZL X Ω₂K
      (fun ζ => ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ) hξc.measurable.enorm
      (fun x t k ζ => (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))
      hS
      (fun t k ζ => (∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))
      c hc0 hcT (fun t k ζ => (core t ζ k).2.symm) hfin
  ·
    refine Eq.trans (TorusUnfold.integral4_move_x_inside' L νZL X Ω₂K (fun ζ => ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)) hξc.measurable
      (fun x t k ζ => (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) hS hfin) ?_
    beta_reduce

    have inner : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)),
        (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * (∫ x in X, (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂(adelicAddHaar (𝓞 L) L)) ∂νZL) =
          (c.toReal : ℂ) * ∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL := by
      intro t k
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      beta_reduce
      rw [(core t ζ k).2]
      ring
    have step : ∀ (t : (AdeleRing (𝓞 L) L)ˣ),
        (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * (∫ x in X, (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂(adelicAddHaar (𝓞 L) L)) ∂νZL) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ) ∂(maximalCompactHaar L)) =
          (c.toReal : ℂ) * ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
            (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ) ∂(maximalCompactHaar L) := by
      intro t
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      beta_reduce
      rw [inner t k, mul_assoc]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => step t)

end XMergeAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub.R1FibreUnfold"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm AutomorphicForm.AdelicTracePushforward AutomorphicForm.TwistedBruhat in

open scoped TensorProduct Pointwise ENNReal NNReal in
theorem solution
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤)  :
   (∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) ∧
    (∫ x in X, ∫ t in Ω₂K, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      (c.toReal : ℂ) * ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)) :=
  XMergeAssembly.xmerge_main K L νZL ΩL hΩL D σ hgen ξL hξc hξt φ hφc hφs R X Ω₂K hX hΩ₂Km hΩ₂K μK hμK1 c hc0 hcT hc hfin

end
end
end
end S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub (solution)
