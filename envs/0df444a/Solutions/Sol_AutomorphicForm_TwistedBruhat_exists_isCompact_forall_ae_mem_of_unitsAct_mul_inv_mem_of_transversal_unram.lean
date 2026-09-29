-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/53794a61-8cc7-5d73-82f6-d3de1c20fe94

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal
import Theorems.Thm_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
import Theorems.Thm_NumberField_Idele_continuous_semiLocalIdele_and_continuous_archSemiLocalIdele
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
import Theorems.Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v))
    (Cd : Set (AdeleRing (𝓞 L) L)ˣ) (hCd : IsCompact Cd) (j : Fin n) :
    ∃ Ct : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Ct ∧
      ∀ᵐ t ∂(τ j), M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹ ∈ Cd → t ∈ Ct := by
  classical
  obtain ⟨hcontF, hcontA⟩ := NumberField.Idele.continuous_semiLocalIdele_and_continuous_archSemiLocalIdele K L
  have hCfin : ∀ v : HeightOneSpectrum (𝓞 K),
      IsCompact (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v '' Cd) := fun v => hCd.image (hcontF v)
  have hCarch : ∀ v : InfinitePlace K,
      IsCompact (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v '' Cd) := fun v => hCd.image (hcontA v)
  choose Bfin hBfin using fun v : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem K L σ hgen v (πs j v) _ (hCfin v)
  choose Barch hBarch using fun v : InfinitePlace K =>
    AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem K L σ hgen v _ (hCarch v)
  refine ⟨{t | (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ Barch v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ Bfin v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ →
        AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)},
    NumberField.Idele.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem K L Barch (fun v => (hBarch v).1)
      Sτ Bfin (fun v _ => (hBfin v).1), ?_⟩
  filter_upwards [AutomorphicForm.TwistedBruhat.ae_mem_structuredBox_of_transversal K L Sτ n c τ τfin τarch πs hcpos
    hlev hτfin hτ0 hgood hgood' hbad harch hfac3 j] with t ht
  intro hmem
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ht.2.2 v hv⟩
  · refine (hBarch v).2 _ (ht.1 v) ?_
    rw [← AutomorphicForm.TransversalMeasure.archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm K L D σ v t]
    refine ⟨AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v
      (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹), ⟨_, hmem, rfl⟩, ?_⟩
    rw [map_mul, map_inv, Units.val_mul]
  · refine (hBfin v).2 _ (ht.2.1 v hv) ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹, hmem, ?_⟩
    rw [map_mul, map_inv]
    congr 1
    exact Units.ext
      ((AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
        K L D σ v).2.1 t)

end S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram (solution)
