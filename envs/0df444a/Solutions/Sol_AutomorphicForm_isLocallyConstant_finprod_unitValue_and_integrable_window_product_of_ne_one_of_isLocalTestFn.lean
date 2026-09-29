-- Prove2me | solution 1 for AutomorphicForm.isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f3cb4a66-9a63-5111-a962-82083af8d803

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
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_tsupport_subset_units_eq_of_isWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))

    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

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

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))
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

    (IT : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) (IT u z v))
    (IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v))
    :
    ∀ (u : Kˣ), (u : K) ≠ 1 →
      IsLocallyConstant (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) ∧
      ∀ (d : (AdeleRing (𝓞 K) K)ˣ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((∏ v ∈ T, IT u (z * d) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u (z * d) v) *
          ((JA' u (z * d) - (Module.finrank K L : ℂ) * JA u (z * d)) * ∏ v ∈ SK, IF u (z * d) v +
            IA u (z * d) * ∑ v ∈ SK, (JF' u (z * d) v - (Module.finrank K L : ℂ) * JF u (z * d) v) *
              ∏ v' ∈ SK.erase v, IF u (z * d) v'))) νZK := by
  intro u hu1
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

  obtain ⟨Φ, hΦs, hΦc, hΦu, hΦCa, hΦall⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
      K νZK faK hfaK cτK hcτK νA hνAh τG hτG hτGc τA hτA τF hτF hτF1 cT hcT
      (fun u z hu S' W Wa WS => hT u z S' W Wa WS hu)
  have hΦ := hΦall u hu1
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
      HasCompactSupport Φv ∧ (v ∈ SK → (IsLocallyConstant Φv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
          AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) I →
            (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
              Φv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z))) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Φv, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fSK v) (hfSK v hv) (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
      exact ⟨Φv, h2, fun _ => ⟨h1, h3⟩⟩
    · exact ⟨0, HasCompactSupport.zero, fun h => absurd h hv⟩
  choose Φv hΦvc hΦv using hB2
  have hB4 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      HasCompactSupport Ψv ∧ (v ∈ SK → (IsLocallyConstant Ψv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
          AutomorphicForm.IsWeightedOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) J →
            J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z))) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Ψv, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fSK v) (hfSK v hv) (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
      exact ⟨Ψv, h2, fun _ => ⟨h1, h3⟩⟩
    · exact ⟨0, HasCompactSupport.zero, fun h => absurd h hv⟩
  choose Ψv hΨvc hΨv using hB4
  have hB6 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Ψ'v : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      HasCompactSupport Ψ'v ∧ (v ∈ SK → (IsLocallyConstant Ψ'v ∧
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
          (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) J →
            J = Ψ'v (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
            Ψ'v (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) = 0))) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Ψ'v, h1, h2, h3, h4⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K L v σ hgen hprime u hu1 (φS v) (hφS v hv) (fun z => δF u z v) (fun z => hδF u z hu1 v hv) (fun z => τF' u z v)
          (fun z => hτF' u z v hu1) (fun z => hτF'1 u z v hu1)
      exact ⟨Ψ'v, h2, fun _ => ⟨h1, h3, h4⟩⟩
    · exact ⟨0, HasCompactSupport.zero, fun h => absurd h hv⟩
  choose Ψ'v hΨ'vc hΨ'v using hB6
  have hBT : ∀ v : HeightOneSpectrum (𝓞 K), ∃ ΦT : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      HasCompactSupport ΦT ∧ (v ∈ T → (IsLocallyConstant ΦT ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
          AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) I →
            (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
              ΦT (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z))) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨ΦT, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fT v) (hfT v hv) (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
      exact ⟨ΦT, h2, fun _ => ⟨h1, h3⟩⟩
    · exact ⟨0, HasCompactSupport.zero, fun h => absurd h hv⟩
  choose ΦT hΦTc hΦT using hBT

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
  have hu1v : ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (u : K) ≠ 1 := fun v h =>
    hu1 ((algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one]))
  have hcv0 : ∀ v, cv v ≠ 0 := by
    intro v; rw [hcv]
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 (hu1v v))
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
  have huzc : ∀ v, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
      (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) :=
    fun v => continuous_const.prodMk (hfucc v)

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
    have h := (hΦv v hv).2 z (IF u z v) (hIF u z hu1 v hv)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hcv0 v)]
    exact h
  have hJFeq : ∀ v ∈ SK, ∀ z, JF u z v = Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) :=
    fun v hv z => (hΨv v hv).2 z _ (hJF u z hu1 v hv)
  have hJF'eq : ∀ v ∈ SK, ∀ z, JF' u z v = Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v hv z
    by_cases h : ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ
    · exact (hΨ'v v hv).2.1 z _ h (hJF' u z hu1 v hv h)
    · rw [hJF'0 u z hu1 v hv h, (hΨ'v v hv).2.2 z h]
  have hITeq : ∀ v ∈ T, ∀ z, IT u z v = ((cv v : ℝ) : ℂ)⁻¹ *
      ΦT v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v hv z
    have h := (hΦT v hv).2 z (IT u z v) (hIT u z hu1 v hv)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hcv0 v)]
    exact h

  have hmat : ∀ (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
      ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        Matrix.diagonal ![((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) (u : K),
          ((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v] := by
    intro v z
    rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2]
    have hu' : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = algebraMap K (v.adicCompletion K) (u : K) := rfl
    have h1 : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := rfl
    rw [hu', h1, mul_one]
  have hIUeq : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK ∪ T → ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      IU u z v = if ‖((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧
          ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1 then (((cv v : ℝ) : ℂ))⁻¹ else 0 := by
    intro v hv z
    rw [hcv]
    exact AutomorphicForm.eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal K v
      (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) (algebraMap K (v.adicCompletion K) (u : K)) (hu1v v) _
      (hmat v z) (τF u z v) (hτF u z v hu1) (hτF1 u z v hu1) (IU u z v) (hIU u z hu1 v hv)

  have hcomp_mul : ∀ (z e : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      (((z * e : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
        ((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v * ((e : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v :=
    fun _ _ _ => rfl
  have hcomp_inv : ∀ (e : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      ((e : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
        (((e⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
    intro e v
    have h : ((e : AdeleRing (𝓞 K) K) * ((e⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = 1 := Units.mul_inv e
    calc _ = (((e : AdeleRing (𝓞 K) K) * ((e⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) v := rfl
      _ = ((1 : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by rw [h]
      _ = 1 := rfl
  have hnv : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K), ‖x‖ = 1 ↔ Valued.v x = 1 := by
    intro v x
    constructor
    · intro h
      exact le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h.le) (Valued.toNormedField.one_le_norm_iff.1 h.ge)
    · intro h
      exact le_antisymm (Valued.toNormedField.norm_le_one_iff.2 h.le) (Valued.toNormedField.one_le_norm_iff.2 h.ge)

  have hmemU : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (e : (AdeleRing (𝓞 K) K)ˣ),
      e ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K S → ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖((e : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    intro S e he v hv
    have h := (NumberField.AdeleRing.mem_unitIdelesOutside_iff S e).1 he v hv
    have h1 : Valued.v (((e : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1 h.1
    have h2 : Valued.v ((((e⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1 h.2
    rw [hnv]
    apply le_antisymm h1
    have h3 := mul_le_mul_right h2 (Valued.v (((e : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
    rw [← map_mul, hcomp_inv e v, map_one, mul_one] at h3
    exact h3

  have hmemU' : ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (y : (AdeleRing (𝓞 K) K)ˣ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ‖((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1) →
        y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K S := by
    intro S y hy
    rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
    intro v hv
    have h1 := (hnv v _).1 (hy v hv)
    have h2 : Valued.v ((((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
      have := congrArg Valued.v (hcomp_inv y v)
      rw [map_mul, h1, one_mul, map_one] at this
      exact this
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).2 h1.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).2 h2.le⟩

  have hcofin : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      {v : HeightOneSpectrum (𝓞 K) | ¬ ‖((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1}.Finite := by
    intro y
    have hu : IsUnit ((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) :=
      ⟨Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom y, rfl⟩
    have hf := Filter.eventually_cofinite.1 (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.1 hu).2
    refine hf.subset fun v hv => ?_
    simp only [Set.mem_setOf_eq] at hv ⊢
    exact fun h => hv ((hnv v _).2 h)

  obtain ⟨PU, hPU⟩ : ∃ PU : (AdeleRing (𝓞 K) K)ˣ → ℂ,
      PU = fun z => ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v := ⟨_, rfl⟩
  have hinv : ∀ (y e : (AdeleRing (𝓞 K) K)ˣ),
      e ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))) → PU (y * e) = PU y := by
    intro y e he
    rw [hPU]
    refine finprod_congr fun v => finprod_congr fun hv => ?_
    have hvS : v ∉ (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by exact_mod_cast hv
    have he1 := hmemU _ e he v hvS
    rw [hIUeq v hv (y * e), hIUeq v hv y, hcomp_mul, norm_mul, he1, mul_one]
  have hUo : IsOpen (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
      Set (AdeleRing (𝓞 K) K)ˣ) := NumberField.Idele.isOpen_unitIdelesOutside K _
  have hA : IsLocallyConstant PU := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun x' => x⁻¹ * x') ⁻¹'
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ),
      hUo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · show x⁻¹ * x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K)))
      rw [inv_mul_cancel]; exact Subgroup.one_mem _
    · intro x' hx'
      have h := hinv x (x⁻¹ * x') hx'
      rw [mul_inv_cancel_left] at h
      exact h
  refine ⟨by rw [← hPU]; exact hA, ?_⟩

  intro d ξ hξc

  have hcIA : Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => IA u y := by
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => IA u y) = fun y => ((N : ℝ) : ℂ)⁻¹ * Φ (pz y) from funext hIAeq]
    exact continuous_const.mul (hΦs.continuous.comp hpzc)
  have hcJA : Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => JA u y := by
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => JA u y) = fun y => Ψ (pz y) from funext hJAeq]
    exact hΨc.comp hpzc
  have hcJA' : Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => JA' u y := by
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => JA' u y) = fun y => Ψ' (pz y) from funext hJA'eq]
    exact hΨ'c.comp hpzc
  have hcIF : ∀ v ∈ SK, Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => IF u y v := by
    intro v hv
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => IF u y v) =
        fun y => ((cv v : ℝ) : ℂ)⁻¹ * Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y)
        from funext (hIFeq v hv)]
    exact continuous_const.mul ((hΦv v hv).1.continuous.comp (huzc v))
  have hcJF : ∀ v ∈ SK, Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => JF u y v := by
    intro v hv
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => JF u y v) =
        fun y => Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) from funext (hJFeq v hv)]
    exact (hΨv v hv).1.continuous.comp (huzc v)
  have hcJF' : ∀ v ∈ SK, Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => JF' u y v := by
    intro v hv
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => JF' u y v) =
        fun y => Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) from funext (hJF'eq v hv)]
    exact (hΨ'v v hv).1.continuous.comp (huzc v)
  have hcIT : ∀ v ∈ T, Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => IT u y v := by
    intro v hv
    rw [show (fun y : (AdeleRing (𝓞 K) K)ˣ => IT u y v) =
        fun y => ((cv v : ℝ) : ℂ)⁻¹ * ΦT v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y)
        from funext (hITeq v hv)]
    exact continuous_const.mul ((hΦT v hv).1.continuous.comp (huzc v))

  obtain ⟨B, hB⟩ : ∃ B : (AdeleRing (𝓞 K) K)ˣ → ℂ, B = fun y =>
    (JA' u y - (Module.finrank K L : ℂ) * JA u y) * ∏ v ∈ SK, IF u y v +
      IA u y * ∑ v ∈ SK, (JF' u y v - (Module.finrank K L : ℂ) * JF u y v) * ∏ v' ∈ SK.erase v, IF u y v' := ⟨_, rfl⟩
  obtain ⟨Wf, hWf⟩ : ∃ Wf : (AdeleRing (𝓞 K) K)ˣ → ℂ, Wf = fun y => (∏ v ∈ T, IT u y v) * PU y * B y := ⟨_, rfl⟩
  have hBc : Continuous B := by
    rw [hB]
    refine Continuous.add ?_ ?_
    · exact (hcJA'.sub (continuous_const.mul hcJA)).mul (continuous_finsetProd SK hcIF)
    · refine hcIA.mul ?_
      refine continuous_finsetSum SK fun v hv => ?_
      exact ((hcJF' v hv).sub (continuous_const.mul (hcJF v hv))).mul
        (continuous_finsetProd (SK.erase v) fun v' hv' => hcIF v' (Finset.mem_of_mem_erase hv'))
  have hWc : Continuous Wf := by
    rw [hWf]
    exact ((continuous_finsetProd T hcIT).mul hA.continuous).mul hBc

  obtain ⟨CaΦ, hCaΦ, hCaΦs⟩ := hΦCa
  obtain ⟨CaΨ, hCaΨ, hCaΨs⟩ := hΨCa
  obtain ⟨CaΨ', hCaΨ', hCaΨ's⟩ := hΨ'Ca
  obtain ⟨Ca, hCa⟩ : ∃ Ca : Set (InfiniteAdeleRing K)ˣ, Ca = Prod.snd '' (CaΦ ∪ CaΨ ∪ CaΨ') := ⟨_, rfl⟩
  have hCac : IsCompact Ca := by rw [hCa]; exact ((hCaΦ.union hCaΨ).union hCaΨ').image continuous_snd
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K), Cf = fun v =>
    (fun q : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ => ((q.2 : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ''
      (tsupport (Φv v) ∪ tsupport (Ψv v) ∪ tsupport (Ψ'v v) ∪ tsupport (ΦT v)) := ⟨_, rfl⟩
  have hCfc : ∀ v ∈ SK ∪ T, IsCompact (Cf v) := fun v _ => by
    rw [hCf]
    exact ((((hΦvc v).isCompact.union (hΨvc v).isCompact).union (hΨ'vc v).isCompact).union (hΦTc v).isCompact).image
      (Units.continuous_val.comp continuous_snd)
  have hCf0 : ∀ v ∈ SK ∪ T, (0 : v.adicCompletion K) ∉ Cf v := by
    intro v _ h0
    rw [hCf] at h0
    obtain ⟨q, -, hq⟩ := h0
    exact q.2.ne_zero hq
  have hTc := NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
    K (SK ∪ T) Ca hCac Cf hCfc hCf0
  obtain ⟨Tset, hTset⟩ : ∃ Tset : Set (AdeleRing (𝓞 K) K)ˣ, Tset = ({z : (AdeleRing (𝓞 K) K)ˣ |
        Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca ∧
        ∀ v ∈ SK ∪ T, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩
      ↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) := ⟨_, rfl⟩
  rw [← hTset] at hTc

  have harch : ∀ (F : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (C : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)),
      (∀ p ∈ tsupport F, ∃ q ∈ C,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (pz z) ≠ 0 → Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Prod.snd '' C := by
    intro F C hC z hz
    obtain ⟨q, hq, hpq⟩ := hC (pz z) (subset_tsupport F hz)
    refine ⟨q, hq, ?_⟩
    have h1 := congrFun hpq 1
    simp only [hpz, hι, Matrix.cons_val_one] at h1
    have h2 := (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective h1
    apply Units.ext
    rw [Units.coe_map]
    exact h2.symm

  have hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (F : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ),
      tsupport F ⊆ tsupport (Φv v) ∪ tsupport (Ψv v) ∪ tsupport (Ψ'v v) ∪ tsupport (ΦT v) →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) ≠ 0 →
        (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v := by
    intro v F hF z hz
    rw [hCf]
    refine ⟨(uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z), hF (subset_tsupport F hz), ?_⟩
    simp only [NumberField.AdeleRing.val_finiteUnitsComponent]

  have hPUfin : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      (fun v : HeightOneSpectrum (𝓞 K) => ∏ᶠ (_ : v ∉ SK ∪ T), IU u y v).HasFiniteMulSupport := by
    intro y
    have hu0 : ((u : K) - 1) ≠ 0 := sub_ne_zero.2 hu1
    refine ((hcofin y).union ((hcofin (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)).union
      (hcofin (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) hu0))))).subset
      fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨hy1, hyu', hyu1'⟩ := hcon
    apply hv
    by_cases hvS : v ∉ SK ∪ T
    · rw [finprod_eq_if, if_pos hvS, hIUeq v hvS y]
      have e1 : ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1 := by
        have : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u : (AdeleRing (𝓞 K) K)ˣ) :
            AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = algebraMap K (v.adicCompletion K) (u : K) := rfl
        rw [← this]; exact hyu'
      have e2 : cv v = 1 := by
        have : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) hu0) :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
            algebraMap K (v.adicCompletion K) ((u : K) - 1) := rfl
        rw [hcv]
        rw [this, map_sub, map_one] at hyu1'
        exact hyu1'
      rw [if_pos ⟨hy1, e1⟩, e2]
      simp
    · rw [finprod_eq_if, if_neg hvS]
  have hPU_units : ∀ y : (AdeleRing (𝓞 K) K)ˣ, PU y ≠ 0 →
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(SK ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by
    intro y hy
    refine hmemU' _ y fun v hv => ?_
    have hvS : v ∉ SK ∪ T := by exact_mod_cast hv
    by_contra hne
    apply hy
    rw [hPU]
    refine finprod_eq_zero (fun v : HeightOneSpectrum (𝓞 K) => ∏ᶠ (_ : v ∉ SK ∪ T), IU u y v) v ?_ (hPUfin y)
    show (∏ᶠ (_ : v ∉ SK ∪ T), IU u y v) = 0
    rw [finprod_eq_if, if_pos hvS, hIUeq v hvS y, if_neg (fun h => hne h.1)]

  have hWsupp : ∀ y : (AdeleRing (𝓞 K) K)ˣ, Wf y ≠ 0 → y ∈ Tset := by
    intro y hWy
    have hWfy : Wf y = (∏ v ∈ T, IT u y v) * PU y * B y := by rw [hWf]
    have hPT : (∏ v ∈ T, IT u y v) ≠ 0 := by
      intro h0; apply hWy; rw [hWfy, h0, zero_mul, zero_mul]
    have hPUy : PU y ≠ 0 := by
      intro h0; apply hWy; rw [hWfy, h0, mul_zero, zero_mul]
    have hbr : B y ≠ 0 := by
      intro h0; apply hWy; rw [hWfy, h0, mul_zero]
    rw [hTset]
    refine ⟨⟨?_, ?_⟩, hPU_units y hPUy⟩
    ·
      have hne : Φ (pz y) ≠ 0 ∨ Ψ (pz y) ≠ 0 ∨ Ψ' (pz y) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2, h3⟩ := hcon
        apply hbr
        simp only [hB]
        rw [hJA'eq, hJAeq, hIAeq, h1, h2, h3]
        simp
      rw [hCa, Set.image_union, Set.image_union]
      rcases hne with h | h | h
      · exact Or.inl (Or.inl (harch Φ CaΦ hCaΦs y h))
      · exact Or.inl (Or.inr (harch Ψ CaΨ hCaΨs y h))
      · exact Or.inr (harch Ψ' CaΨ' hCaΨ's y h)
    ·
      intro v hvS
      have hvS' : v ∈ SK ∨ v ∈ T := Finset.mem_union.1 hvS
      by_cases hvK : v ∈ SK
      · have hne : Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 ∨
            Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 ∨
            Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 := by
          by_contra hcon
          push Not at hcon
          obtain ⟨h1, h2, h3⟩ := hcon
          have e1 : IF u y v = 0 := by rw [hIFeq v hvK, h1, mul_zero]
          have e2 : JF u y v = 0 := by rw [hJFeq v hvK, h2]
          have e3 : JF' u y v = 0 := by rw [hJF'eq v hvK, h3]
          apply hbr
          simp only [hB]
          have hp : ∏ w ∈ SK, IF u y w = 0 := Finset.prod_eq_zero hvK e1
          have hs : ∑ w ∈ SK, (JF' u y w - (Module.finrank K L : ℂ) * JF u y w) * ∏ v' ∈ SK.erase w, IF u y v' = 0 := by
            refine Finset.sum_eq_zero fun w hw => ?_
            by_cases hwv : w = v
            · subst hwv; rw [e2, e3]; simp
            · rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hwv h.symm, hvK⟩) e1, mul_zero]
          rw [hp, hs, mul_zero, mul_zero, add_zero]
        rcases hne with h | h | h
        · exact hfin v (Φv v) (fun p hp => Or.inl (Or.inl (Or.inl hp))) y h
        · exact hfin v (Ψv v) (fun p hp => Or.inl (Or.inl (Or.inr hp))) y h
        · exact hfin v (Ψ'v v) (fun p hp => Or.inl (Or.inr hp)) y h
      · have hvT : v ∈ T := hvS'.resolve_left hvK
        have hne : ΦT v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v y) ≠ 0 := by
          intro h0
          apply hPT
          exact Finset.prod_eq_zero hvT (by rw [hITeq v hvT, h0, mul_zero])
        exact hfin v (ΦT v) (fun p hp => Or.inr hp) y hne

  obtain ⟨G, hG⟩ : ∃ G : (AdeleRing (𝓞 K) K)ˣ → ℂ, G = fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Wf (z * d) := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]
    exact hξc.mul (hWc.comp (continuous_id.mul continuous_const))
  obtain ⟨Tset', hTset'⟩ : ∃ Tset' : Set (AdeleRing (𝓞 K) K)ˣ, Tset' = (fun y => y * d⁻¹) '' Tset := ⟨_, rfl⟩
  have hTc2 : IsCompact Tset' := by rw [hTset']; exact hTc.image (continuous_id.mul continuous_const)
  have hGsupp : ∀ z, G z ≠ 0 → z ∈ Tset' := by
    intro z hz
    have hW : Wf (z * d) ≠ 0 := by
      intro h0; apply hz; rw [hG]; show _ * Wf (z * d) = 0; rw [h0, mul_zero]
    rw [hTset']
    exact ⟨z * d, hWsupp _ hW, by simp [mul_assoc]⟩
  have hTm' : MeasurableSet Tset' := hTc2.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hTc2.exists_bound_of_continuousOn hGc.continuousOn
  have hint : IntegrableOn G Tset' νZK := by
    refine Measure.integrableOn_of_bounded hTc2.measure_lt_top.ne hGc.aestronglyMeasurable (M := M) ?_
    exact ae_restrict_of_forall_mem hTm' fun z hz => hM z hz
  have hI : Integrable G νZK :=
    hint.integrable_of_forall_notMem_eq_zero fun z hz => by
      by_contra hne
      exact hz (hGsupp z hne)

  have hfun : (fun z : (AdeleRing (𝓞 K) K)ˣ =>
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IT u (z * d) v) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u (z * d) v) *
        ((JA' u (z * d) - (Module.finrank K L : ℂ) * JA u (z * d)) * ∏ v ∈ SK, IF u (z * d) v +
          IA u (z * d) * ∑ v ∈ SK, (JF' u (z * d) v - (Module.finrank K L : ℂ) * JF u (z * d) v) *
            ∏ v' ∈ SK.erase v, IF u (z * d) v'))) = G := by
    funext z
    simp only [hG, hWf, hPU, hB]
  rw [hfun]
  exact hI

end S_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn (solution)
