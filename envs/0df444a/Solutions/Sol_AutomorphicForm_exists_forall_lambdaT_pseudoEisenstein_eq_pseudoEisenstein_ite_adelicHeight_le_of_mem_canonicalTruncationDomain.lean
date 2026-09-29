-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4c98da06-2e91-5acf-a749-f82ebd08e030

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicHeight
open NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel
open IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R1ArthurSecondFormula

variable {F : Type} [Field F] [NumberField F]

theorem pow_le_adelicHeight_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : 0 ≤ c)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂) :
    c ^ (∑ w : InfinitePlace F, w.mult) ≤ adelicHeight F g := by
  obtain ⟨hK, hfloor, -⟩ :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet (F := F) (u := u) (d₁ := d₁) (d₂ := d₂) hc hg
  rw [adelicHeight_eq_archHeight_of_mem hK]
  exact hfloor

variable (F) in

theorem exists_forall_adelicHeight_globalPoints_mul_le_exp {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ g ∈ canonicalTruncationDomain F α β, ∀ γ : GL (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
        adelicHeight F (globalPoints (𝓞 F) F γ * g) ≤ Real.exp R := by
  obtain ⟨hc, hTc, hcov, -, -⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hα hαβ
  obtain ⟨κ, K, hκ, hκK⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F
      (canonicalTruncationTranslates F α β) hTc
  set c := canonicalTruncationFloor F α β with hcdef
  set h₀ : ℝ := κ * c ^ (∑ w : InfinitePlace F, w.mult) with hh₀
  have hh₀pos : 0 < h₀ := mul_pos hκ (pow_pos hc _)
  have hfloor : ∀ g ∈ canonicalTruncationDomain F α β, h₀ ≤ adelicHeight F g := by
    intro g hg
    have hg' := hcov hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg'
    obtain ⟨y, hy, x, hx, rfl⟩ := hg'
    calc h₀ = κ * c ^ (∑ w : InfinitePlace F, w.mult) := rfl
      _ ≤ κ * adelicHeight F x :=
          mul_le_mul_of_nonneg_left (pow_le_adelicHeight_of_mem_centreCutSiegelSet hc.le hx) hκ.le
      _ ≤ adelicHeight F (x * y) := (hκK x y hy).1
  refine ⟨Real.log h₀⁻¹, fun R hR g hg γ hγ => ?_⟩
  have hHg : 0 < adelicHeight F g := adelicHeight_pos g
  have hle : adelicHeight F (globalPoints (𝓞 F) F γ * g) ≤ (adelicHeight F g)⁻¹ := by
    rw [← one_div, le_div_iff₀ hHg]
    exact adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ g
  calc adelicHeight F (globalPoints (𝓞 F) F γ * g) ≤ (adelicHeight F g)⁻¹ := hle
    _ ≤ h₀⁻¹ := (inv_le_inv₀ hHg hh₀pos).mpr (hfloor g hg)
    _ = Real.exp (Real.log h₀⁻¹) := (Real.exp_log (inv_pos.mpr hh₀pos)).symm
    _ ≤ Real.exp R := Real.exp_le_exp.mpr hR

theorem adelicWeyl_mul_unipotentGL2_eq (ξ : F) :
    adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 ξ) := by
  rw [map_mul]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints_apply]
  simp only [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField F] in
theorem gl2Weyl_mul_unipotentGL2_apply_one_zero (ξ : F) :
    ((gl2Weyl * unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  rw [Units.val_mul, gl2Weyl_val, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end R1ArthurSecondFormula

open R1ArthurSecondFormula in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ),
    ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      @AutomorphicForm.lambdaT _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
        (AutomorphicForm.pseudoEisenstein F φ) g
      = AutomorphicForm.pseudoEisenstein F
          (fun x => if NumberField.AdelicHeight.adelicHeight F x ≤ Real.exp R then φ x
            else -(((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x)) g := by
  intro αm hαm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  obtain ⟨R₀, hR₀⟩ := exists_forall_adelicHeight_globalPoints_mul_le_exp F hα hαβ
  refine ⟨R₀, fun R hR μ ν hμ hν s hs φ hφ hφc g hg => ?_⟩

  have hCT := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm
    μ ν hμ hν s hs φ hφ hφc g

  have hlow : ∀ ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) ≤ Real.exp R := by
    intro ξ
    rw [adelicWeyl_mul_unipotentGL2_eq]
    refine hR₀ R hR g hg _ ?_
    rw [gl2Weyl_mul_unipotentGL2_apply_one_zero]
    exact one_ne_zero

  set φT : AdelicGL2 (𝓞 F) F → ℂ := fun x => if adelicHeight F x ≤ Real.exp R then φ x
    else -(((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x) with hφT
  have hsum : (∑' ξ : F, φT (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      = ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
    refine tsum_congr fun ξ => ?_
    simp only [hφT, if_pos (hlow ξ)]
  show AutomorphicForm.lambdaT _ (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R)
      (pseudoEisenstein F φ) g = pseudoEisenstein F φT g
  rw [pseudoEisenstein_apply, hsum]
  by_cases hgT : adelicHeight F g ≤ Real.exp R
  · rw [lambdaT_apply_of_le _ _ hgT, pseudoEisenstein_apply]
    simp only [hφT, if_pos hgT]
  · rw [lambdaT_apply_of_lt _ _ (lt_of_not_ge hgT)]
    have goal' : pseudoEisenstein F φ g - (φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g)
        = φT g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
      rw [pseudoEisenstein_apply]
      simp only [hφT, if_neg hgT]
      ring
    convert goal' using 2
    all_goals first | rfl | exact hCT

end S_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain (solution)
