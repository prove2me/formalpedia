-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a50aeea9-bbcd-5d0f-8d03-7010dbe6f8a2

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
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_tracePushforward_eq_indicator_prod_twistedLocalFactor_unram
import Theorems.Thm_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
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
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1)
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
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v)) :
    ∃ (Sx : Finset (HeightOneSpectrum (𝓞 K))) (g : Fin n → InfiniteAdeleRing K → ℂ)
      (h₀ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ),
      S ∪ T ⊆ Sx ∧
      (∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (j : Fin n),
        ((fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) ∈ NumberField.AdelicFourier.schwartzBruhat K ∧
          HasCompactSupport (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x))) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ (j : Fin n) (y : (AdeleRing (𝓞 K) K)ˣ) (θ : ℝ),
          (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0))‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂(τ j)) ≠ ⊤ ∧
            (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
            ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)
                (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
              (if θ < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) := by
  obtain ⟨Sx, g, h₀, hSx, hSB, hPT⟩ :=
    AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_tracePushforward_eq_indicator_prod_twistedLocalFactor_unram K L νZL D σ hgen SL ξL hSL hξc hξt S φa φS μK hξσ T hT ws ns rTs zs Sτ hSτ n c τ τfin τarch πs hcpos hlev hτfin hτ0 hgood hgood' hbad harch hfac3
  refine ⟨Sx, g, h₀, hSx, hSB, ?_⟩
  intro ks js φ φf hφ j y θ
  obtain ⟨hfin, heq⟩ :=
    AutomorphicForm.TwistedBruhat.forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram K L νZL D σ hgen SL ξL hSL hξc hξt S φa φS μK hξσ T hT ws ns rTs zs Sτ hSτ n c τ τfin τarch πs hcpos hlev hτfin hτ0 hgood hgood' hbad harch hfac3
      ks js φ φf hφ j y θ
  refine ⟨hfin, ?_⟩
  rw [heq]
  have hpt := fun r => (hPT ks js φ φf hφ j r).2
  simp only [hpt]

end S_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram (solution)
