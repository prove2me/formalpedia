-- Prove2me | solution 1 for AutomorphicForm.integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cf82a20c-3fb3-55a9-9d44-4c16a3b6b853

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_tsupport_subset_units_eq_of_isWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))

    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS = Measure.map (NumberField.Idele.partAt K SK)
      (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)

    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))

    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))

    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K) (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0)
    (u : Kˣ) (hu1 : (u : K) ≠ 1) :
    Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        ((JA' u zS - (Module.finrank K L : ℂ) * JA u zS) * ∏ v ∈ SK, IF u zS v +
          IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v')) PZ.νS := by
  classical

  have hνAh : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA := by
    have h : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))
        (AutomorphicForm.archHaarK K) := by
      letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      haveI := AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing K)
      haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
        inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
      haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
        inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
      haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) :=
        Units.isClosedEmbedding_embedProduct.locallyCompactSpace
      unfold AutomorphicForm.archHaarK
      infer_instance
    exact hνA.symm ▸ h

  obtain ⟨Φ, hΦs, hΦc, hΦu, hΦCa, hΦ⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
      K νZK u hu1 faK hfaK cτK hcτK νA hνAh (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1)
      (τA u) (fun z => hτA u z hu1) (τF u) (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT
      (fun z S' W Wa WS => hT u z S' W Wa WS hu1)
  obtain ⟨Ψ, hΨc, hΨs, hΨu, hΨCa, hΨ⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_tsupport_subset_units_eq_of_isWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
      K νZK u hu1 faK hfaK cτK hcτK νA hνAh (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1)
      (τA u) (fun z => hτA u z hu1) (τF u) (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT
      (fun z S' W Wa WS => hT u z S' W Wa WS hu1)
  obtain ⟨Ψ', hΨ'c, hΨ's, hΨ'u, hΨ'Ca, hΨ', hΨ'0⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
      K νZK u hu1 cτK hcτK (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1)
      (τA u) (fun z => hτA u z hu1) (τF u) (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT
      (fun z S' W Wa WS => hT u z S' W Wa WS hu1)
      L σ hgen hprime φa hφa νA' hνA' (δA u) (fun z => hδA u z hu1) (τA' u) (fun z => hτA' u z hu1)
      (fun z => hτA'c u z hu1)

  have hB2 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Φv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      v ∈ SK → (IsLocallyConstant Φv ∧ HasCompactSupport Φv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
          AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) I →
            (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
              Φv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Φv, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fSK v) (hfSK v hv) (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
      exact ⟨Φv, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Φv hΦv using hB2
  have hB4 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      v ∈ SK → (IsLocallyConstant Ψv ∧ HasCompactSupport Ψv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
          AutomorphicForm.IsWeightedOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) J →
            J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Ψv, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fSK v) (hfSK v hv) (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
      exact ⟨Ψv, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Ψv hΨv using hB4
  have hB6 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Ψ'v : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      v ∈ SK → (IsLocallyConstant Ψ'v ∧ HasCompactSupport Ψ'v ∧
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
          (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) J →
            J = Ψ'v (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
            Ψ'v (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) = 0)) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Ψ'v, h1, h2, h3, h4⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K L v σ hgen hprime u hu1 (φS v) (hφS v hv) (fun z => δF u z v) (fun z => hδF u z hu1 v hv) (fun z => τF' u z v)
          (fun z => hτF' u z v hu1) (fun z => hτF'1 u z v hu1)
      exact ⟨Ψ'v, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Ψ'v hΨ'v using hB6

  set ι := InfiniteAdeleRing.ringEquiv_mixedSpace K with hι
  set uA : InfiniteAdeleRing K := AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) with huA
  set N : ℝ := ∏ w : InfinitePlace K, ‖uA w - 1‖ ^ w.mult with hN
  set pz : (AdeleRing (𝓞 K) K)ˣ → (Fin 2 → mixedEmbedding.mixedSpace K) := fun z =>
    ![ι uA, ι (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] with hpz
  set uv : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v =>
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u with huv
  set cv : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ with hcv
  have hN0 : N ≠ 0 := by
    rw [hN]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 ?_))
    rw [huA]
    show algebraMap K w.Completion (u : K) ≠ 1
    intro h
    exact hu1 ((algebraMap K w.Completion).injective (by rw [h, map_one]))
  have hcv0 : ∀ v, cv v ≠ 0 := by
    intro v; rw [hcv]
    refine norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => ?_)
    exact hu1 ((algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one]))
  have hIAeq : ∀ z, IA u z = ((N : ℝ) : ℂ)⁻¹ * Φ (pz z) := by
    intro z
    have h := hΦ z (IA u z) (hIA u z hu1)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hN0)]
    exact h
  have hJAeq : ∀ z, JA u z = Ψ (pz z) := fun z => hΨ z _ (hJA u z hu1)
  have hJA'eq : ∀ z, JA' u z = Ψ' (pz z) := by
    intro z
    by_cases h : ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ
    · exact hΨ' z _ h (hJA' u z hu1 h)
    · rw [hJA'0 u z hu1 h, hΨ'0 z h]
  have hIFeq : ∀ v ∈ SK, ∀ z, IF u z v = ((cv v : ℝ) : ℂ)⁻¹ *
      Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v hv z
    have h := (hΦv v hv).2.2 z (IF u z v) (hIF u z hu1 v hv)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hcv0 v)]
    exact h
  have hJFeq : ∀ v ∈ SK, ∀ z, JF u z v = Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) :=
    fun v hv z => (hΨv v hv).2.2 z _ (hJF u z hu1 v hv)
  have hJF'eq : ∀ v ∈ SK, ∀ z, JF' u z v = Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v hv z
    by_cases h : ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ
    · exact (hΨ'v v hv).2.2.1 z _ h (hJF' u z hu1 v hv h)
    · rw [hJF'0 u z hu1 v hv h, (hΨ'v v hv).2.2.2 z h]

  have hpzc : Continuous pz := by
    rw [hpz]
    have h2 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ι (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) :=
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K).comp (continuous_fst.comp Units.continuous_val)
    exact Continuous.matrixVecCons continuous_const
      (Continuous.matrixVecCons h2 (continuous_const : Continuous fun _ : (AdeleRing (𝓞 K) K)ˣ =>
        (![] : Fin 0 → mixedEmbedding.mixedSpace K)))
  have hfucc : ∀ v, Continuous (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v) := by
    intro v
    rw [Units.continuous_iff]
    constructor
    · show Continuous fun x : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      simp only [NumberField.AdeleRing.val_finiteUnitsComponent]
      exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
    · show Continuous fun x : (AdeleRing (𝓞 K) K)ˣ =>
        (((NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v x)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      simp only [← map_inv, NumberField.AdeleRing.val_finiteUnitsComponent]
      exact (RestrictedProduct.continuous_eval v).comp
        (continuous_snd.comp (Units.continuous_val.comp continuous_inv))
  have hcIA : Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => IA u zS := by
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => IA u zS) = fun zS => ((N : ℝ) : ℂ)⁻¹ * Φ (pz zS) from funext hIAeq]
    exact continuous_const.mul (hΦs.continuous.comp hpzc)
  have hcJA : Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => JA u zS := by
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => JA u zS) = fun zS => Ψ (pz zS) from funext hJAeq]
    exact hΨc.comp hpzc
  have hcJA' : Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => JA' u zS := by
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => JA' u zS) = fun zS => Ψ' (pz zS) from funext hJA'eq]
    exact hΨ'c.comp hpzc
  have hcIF : ∀ v ∈ SK, Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => IF u zS v := by
    intro v hv
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => IF u zS v) =
        fun zS => ((cv v : ℝ) : ℂ)⁻¹ * Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v zS)
        from funext (hIFeq v hv)]
    exact continuous_const.mul ((hΦv v hv).1.continuous.comp (continuous_const.prodMk (hfucc v)))
  have hcJF : ∀ v ∈ SK, Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => JF u zS v := by
    intro v hv
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => JF u zS v) =
        fun zS => Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v zS) from funext (hJFeq v hv)]
    exact (hΨv v hv).1.continuous.comp (continuous_const.prodMk (hfucc v))
  have hcJF' : ∀ v ∈ SK, Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => JF' u zS v := by
    intro v hv
    rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => JF' u zS v) =
        fun zS => Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v zS) from funext (hJF'eq v hv)]
    exact (hΨ'v v hv).1.continuous.comp (continuous_const.prodMk (hfucc v))
  set G : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun zS => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      ((JA' u zS - (Module.finrank K L : ℂ) * JA u zS) * ∏ v ∈ SK, IF u zS v +
        IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v')
    with hG
  have hGc : Continuous G := by
    rw [hG]
    refine hξc.mul ((((hcJA'.sub (continuous_const.mul hcJA)).mul (continuous_finset_prod SK hcIF)).add
      (hcIA.mul (continuous_finset_sum SK fun v hv => ((hcJF' v hv).sub (continuous_const.mul (hcJF v hv))).mul
        (continuous_finset_prod (SK.erase v) fun v' hv' => hcIF v' (Finset.mem_of_mem_erase hv'))))))

  obtain ⟨CaΦ, hCaΦ, hCaΦs⟩ := hΦCa
  obtain ⟨CaΨ, hCaΨ, hCaΨs⟩ := hΨCa
  obtain ⟨CaΨ', hCaΨ', hCaΨ's⟩ := hΨ'Ca
  set Ca : Set (InfiniteAdeleRing K)ˣ := Prod.snd '' (CaΦ ∪ CaΨ ∪ CaΨ') with hCa
  have hCac : IsCompact Ca := ((hCaΦ.union hCaΨ).union hCaΨ').image continuous_snd
  set Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v =>
    (fun q : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ => ((q.2 : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ''
      (tsupport (Φv v) ∪ tsupport (Ψv v) ∪ tsupport (Ψ'v v)) with hCf
  have hCfc : ∀ v ∈ SK, IsCompact (Cf v) := fun v hv =>
    (((hΦv v hv).2.1.isCompact.union (hΨv v hv).2.1.isCompact).union (hΨ'v v hv).2.1.isCompact).image
      (Units.continuous_val.comp continuous_snd)
  have hCf0 : ∀ v ∈ SK, (0 : v.adicCompletion K) ∉ Cf v := by
    intro v hv h0
    obtain ⟨q, -, hq⟩ := h0
    exact q.2.ne_zero hq
  have hTc := NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
    K SK Ca hCac Cf hCfc hCf0
  set T : Set (AdeleRing (𝓞 K) K)ˣ := ({z : (AdeleRing (𝓞 K) K)ˣ |
        Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca ∧
        ∀ v ∈ SK, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩
      ↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK : Set (HeightOneSpectrum (𝓞 K))))) with hT

  have harch : ∀ (F : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (C : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)),
      (∀ p ∈ tsupport F, ∃ q ∈ C,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (pz z) ≠ 0 → Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Prod.snd '' C := by
    intro F C hC z hz
    obtain ⟨q, hq, hpq⟩ := hC (pz z) (subset_tsupport F hz)
    refine ⟨q, hq, ?_⟩
    have h1 := congrFun hpq 1
    simp only [hpz, hι, Matrix.cons_val_one, Matrix.head_cons] at h1
    have h2 := (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective h1
    apply Units.ext
    rw [Units.coe_map]
    exact h2.symm

  have hfin : ∀ v ∈ SK, ∀ (F : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ),
      tsupport F ⊆ tsupport (Φv v) ∪ tsupport (Ψv v) ∪ tsupport (Ψ'v v) →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) ≠ 0 →
        (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v := by
    intro v hv F hF z hz
    refine ⟨(uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z), hF (subset_tsupport F hz), ?_⟩
    simp only [NumberField.AdeleRing.val_finiteUnitsComponent]

  have hTsupp : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK : Set (HeightOneSpectrum (𝓞 K))) →
      G (NumberField.Idele.partAt K SK z) ≠ 0 → z ∈ T := by
    intro z hzU hGz
    set y := NumberField.Idele.partAt K SK z with hy
    have hy1 : ((y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 :=
      NumberField.Idele.partAt_fst K SK z
    have hy2 : ∀ v ∈ SK, ((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
        ((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v :=
      fun v hv => NumberField.Idele.partAt_snd_of_mem K SK z hv
    have hbr : (JA' u y - (Module.finrank K L : ℂ) * JA u y) * ∏ v ∈ SK, IF u y v +
        IA u y * ∑ v ∈ SK, (JF' u y v - (Module.finrank K L : ℂ) * JF u y v) * ∏ v' ∈ SK.erase v, IF u y v' ≠ 0 := by
      intro h0; apply hGz; simp only [hG, h0, mul_zero]
    refine ⟨⟨?_, ?_⟩, hzU⟩
    ·
      have hne : Φ (pz y) ≠ 0 ∨ Ψ (pz y) ≠ 0 ∨ Ψ' (pz y) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2, h3⟩ := hcon
        apply hbr
        rw [hJA'eq, hJAeq, hIAeq, h1, h2, h3]
        simp
      have hmem : Units.map (AdelicLevel.adeleArch (𝓞 K) K) y ∈ Ca := by
        rw [hCa, Set.image_union, Set.image_union]
        rcases hne with h | h | h
        · exact Or.inl (Or.inl (harch Φ CaΦ hCaΦs y h))
        · exact Or.inl (Or.inr (harch Ψ CaΨ hCaΨs y h))
        · exact Or.inr (harch Ψ' CaΨ' hCaΨ's y h)
      have hyz : Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z =
          Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) y := by
        apply Units.ext
        rw [Units.coe_map, Units.coe_map]
        exact hy1.symm
      rw [hyz]; exact hmem
    ·
      intro v hv
      have hne : Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 ∨
          Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 ∨
          Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2, h3⟩ := hcon
        have e1 : IF u y v = 0 := by rw [hIFeq v hv, h1, mul_zero]
        have e2 : JF u y v = 0 := by rw [hJFeq v hv, h2]
        have e3 : JF' u y v = 0 := by rw [hJF'eq v hv, h3]
        apply hbr
        have hp : ∏ w ∈ SK, IF u y w = 0 := Finset.prod_eq_zero hv e1
        have hs : ∑ w ∈ SK, (JF' u y w - (Module.finrank K L : ℂ) * JF u y w) * ∏ v' ∈ SK.erase w, IF u y v' = 0 := by
          refine Finset.sum_eq_zero fun w hw => ?_
          by_cases hwv : w = v
          · subst hwv; rw [e2, e3]; simp
          · rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hwv h.symm, hv⟩) e1, mul_zero]
        rw [hp, hs, mul_zero, mul_zero, add_zero]
      have hmem : (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v := by
        rcases hne with h | h | h
        · exact hfin v hv (Φv v) (fun p hp => Or.inl (Or.inl hp)) y h
        · exact hfin v hv (Ψv v) (fun p hp => Or.inl (Or.inr hp)) y h
        · exact hfin v hv (Ψ'v v) (fun p hp => Or.inr hp) y h
      rw [← hy2 v hv]; exact hmem

  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK : Set (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ) with hU
  have hUm : MeasurableSet U := (NumberField.Idele.isOpen_unitIdelesOutside K _).measurableSet
  have hc0 : ENNReal.ofReal PZ.c ≠ 0 := (ENNReal.ofReal_pos.2 PZ.c_pos).ne'
  have hνS : PZ.νS = (ENNReal.ofReal PZ.c)⁻¹ •
      Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict U) := by
    rw [hU, ← hPν, smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul]
  show Integrable G PZ.νS
  rw [hνS]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hc0)
  rw [integrable_map_measure hGc.aestronglyMeasurable (NumberField.Idele.continuous_partAt K SK).measurable.aemeasurable]
  show IntegrableOn (G ∘ NumberField.Idele.partAt K SK) U νZK
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  have hfinT : νZK (U ∩ T) ≠ ⊤ := (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hTc.measure_lt_top).ne
  obtain ⟨M, hM⟩ := (hTc.image (NumberField.Idele.continuous_partAt K SK)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hint : IntegrableOn (G ∘ NumberField.Idele.partAt K SK) (U ∩ T) νZK := by
    refine Measure.integrableOn_of_bounded hfinT
      ((hGc.comp (NumberField.Idele.continuous_partAt K SK)).aestronglyMeasurable) (M := M) ?_
    refine ae_restrict_of_forall_mem (hUm.inter hTm) fun z hz => ?_
    exact hM _ ⟨z, hz.2, rfl⟩
  refine hint.of_forall_diff_eq_zero hUm fun z hz => ?_
  obtain ⟨hzU, hzT⟩ := hz
  by_contra hne
  exact hzT ⟨hzU, hTsupp z (by rw [hU] at hzU; exact hzU) hne⟩

end S_AutomorphicForm_integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one (solution)
