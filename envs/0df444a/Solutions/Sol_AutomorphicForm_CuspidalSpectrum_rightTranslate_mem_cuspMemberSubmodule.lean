-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c0bb3ea5-6a95-54e4-acc9-e6523c6b7f56

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_IsCuspidalFn_rightTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (y : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightTranslate F y φ ∈ cuspMemberSubmodule F Φ₀ ξ := by
  obtain ⟨⟨⟨hmemb, hcusp⟩, hKf⟩, hcont⟩ := hφ
  obtain ⟨hLs, hL2⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hmemb
  obtain ⟨hleft, hcentral⟩ := hLs
  have hRy : ∀ x, rightTranslate F y φ x = φ (x * y) := fun x => rfl

  have hcont' : Continuous (rightTranslate F y φ) := by
    show Continuous fun x => φ (x * y)
    exact hcont.comp (continuous_id.mul continuous_const)

  have hLs' : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightTranslate F y φ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 F) F γ * g * y) = φ (g * y)
      rw [mul_assoc, hleft]
    · show φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * y) = ((ξ z : ℂˣ) : ℂ) * φ (g * y)
      rw [mul_assoc, hcentral]

  have hL2' : MemLp (rightTranslate F y φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    by_cases h0 : φ = 0
    · subst h0
      exact MemLp.zero'
    · obtain ⟨σ, hσ⟩ :=
        AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F Φ₀ ξ φ hmemb hcont h0
      exact (AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀
        hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ ⟨hleft, hcentral⟩ ⟨hleft, hcentral⟩ hcont hcont hL2 hL2 y).1
  have hmemb' : IsAutomorphicFnAt F (fdPins F Φ₀) ξ (rightTranslate F y φ) :=
    (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ _).mpr ⟨hLs', hL2'⟩

  have hcusp' : @IsCuspidalFn _ (fdPins F Φ₀).nS _ _ (fdPins F Φ₀).ν unipotentGL2 (rightTranslate F y φ) :=
    @AutomorphicForm.IsCuspidalFn.rightTranslate _ (fdPins F Φ₀).nS _ _ _ _ _ hcusp y

  have hKf' : IsKfSmooth F (rightTranslate F y φ) := by
    set K : Subgroup (AdelicGL2 (𝓞 F) F) := finiteAdelicGL2Subgroup F with hK
    haveI hKn : K.Normal := by
      rw [hK]
      unfold finiteAdelicGL2Subgroup
      infer_instance

    have hmemc : ∀ k : K, y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y ∈ K := fun k => by
      simpa using hKn.conj_mem (k : AdelicGL2 (𝓞 F) F) k.2 y⁻¹
    let c : K → K := fun k => ⟨y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y, hmemc k⟩
    have hc : Continuous c :=
      (((continuous_const.mul continuous_subtype_val).mul continuous_const)).subtype_mk _
    have hopen : IsOpen ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K) := hKf
    show IsOpen ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk (rightTranslate F y φ) :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)
    have hsub : c ⁻¹' ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)
        ⊆ ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk (rightTranslate F y φ) :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K) := by
      intro k hk
      simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hk ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * y)) hk
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 ⊢
      show φ (x * (k : AdelicGL2 (𝓞 F) F) * y) = φ (x * y)
      have : x * y * (y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y) = x * (k : AdelicGL2 (𝓞 F) F) * y := by group
      rw [this] at h1
      exact h1

    have hH : IsOpen (c ⁻¹' ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)) := hopen.preimage hc

    let chom : K →* K :=
      { toFun := c
        map_one' := by
          refine Subtype.ext ?_
          show y⁻¹ * ((1 : K) : AdelicGL2 (𝓞 F) F) * y = ((1 : K) : AdelicGL2 (𝓞 F) F)
          simp
        map_mul' := fun a b => by
          refine Subtype.ext ?_
          show y⁻¹ * ((a * b : K) : AdelicGL2 (𝓞 F) F) * y
            = (y⁻¹ * (a : AdelicGL2 (𝓞 F) F) * y) * (y⁻¹ * (b : AdelicGL2 (𝓞 F) F) * y)
          simp only [Subgroup.coe_mul]
          group }
    refine Subgroup.isOpen_mono (H₁ := (MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)).comap chom) ?_ ?_
    · intro k hk
      exact hsub hk
    · exact hH
  exact ⟨⟨⟨hmemb', hcusp'⟩, hKf'⟩, hcont'⟩

end S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule (solution)
