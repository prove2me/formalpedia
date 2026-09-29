-- Prove2me | solution 1 for AutomorphicForm.isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/150378ed-280a-5f3f-af3b-b1af4a8aa291

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open NumberField AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : SquaresToXi (𝓞 K) K ⊤ ξK χ)
    (hχt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
        (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξK (chiDet (𝓞 K) K χ) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hclass : IsIdeleClassChar (𝓞 K) K χ := fun u => hχt _ ⟨u, rfl⟩
  have hcont : Continuous (chiDet (𝓞 K) K χ) := by
    have hdet : Continuous (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
      refine Units.continuous_iff.mpr ⟨?_, ?_⟩
      · exact Units.continuous_val.matrix_det
      · have : (fun g : AdelicGL2 (𝓞 K) K => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ).val) =
            fun g => ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det := by
          funext g; rw [← map_inv]; rfl
        rw [this]
        exact (Units.continuous_val.comp continuous_inv).matrix_det
    exact hχc.comp hdet

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => chiDet_globalPoints_mul K χ hclass γ g, fun z g => ?_⟩, ?_⟩
  · rw [chiDet_centralScalar_mul]
    congr 1
    have h := hχ z
    rw [← Units.val_pow_eq_pow_val, h]
    rfl
  · show MemLp (chiDet (𝓞 K) K χ) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
    refine (memLp_top_of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun g => ?_)).mono_exponent le_top
    show ‖((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ ≤ 1
    rw [hχu]

end S_AutomorphicForm_isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous (solution)
