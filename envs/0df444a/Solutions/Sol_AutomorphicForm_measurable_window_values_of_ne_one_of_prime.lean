-- Prove2me | solution 1 for AutomorphicForm.measurable_window_values_of_ne_one_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/db9d66a4-0f6d-533e-b2ea-bd665217d967

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
import Theorems.Thm_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measurable_window_values_of_ne_one_of_prime
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
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ φa faK)
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fSK v))

    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))
    (hmatchT : ∀ v ∈ T, ∃ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv (fT v))
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T →
      AutomorphicForm.AreMatchingLocal K L v σ
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))

    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (SK ∪ T) f faK ff (fun v => if v ∈ T then fT v else fSK v))

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
      Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => IA u z) ∧
      Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => JA u z) ∧
      Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => JA' u z) ∧
      (∀ v ∈ SK,
        Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => IF u z v) ∧
        Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => JF u z v) ∧
        Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => JF' u z v)) ∧
      (∀ v ∈ T, Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => IT u z v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → Measurable (fun z : (AdeleRing (𝓞 K) K)ˣ => IU u z v)) := by
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

  have hind : ∀ v : HeightOneSpectrum (𝓞 K),
      AutomorphicForm.IsLocalTestFn K v ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) := by
    intro v
    have h := (AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
      K v 1).1
    simp only [map_one, inv_one, one_mul] at h
    exact h

  have hfinplain : ∀ (v : HeightOneSpectrum (𝓞 K)) (fv : GL (Fin 2) (v.adicCompletion K) → ℂ),
      AutomorphicForm.IsLocalTestFn K v fv →
      ∃ Φv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Φv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
          AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) fv I →
            (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
              Φv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v fv hfv
    obtain ⟨Φv, h1, -, h3⟩ :=
      AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
        K v u hu1 fv hfv (fun z => τF u z v) (fun z => hτF u z v hu1) (fun z => hτF1 u z v hu1)
    exact ⟨Φv, h1, h3⟩
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

  have hplainMeas : ∀ (v : HeightOneSpectrum (𝓞 K)) (fv : GL (Fin 2) (v.adicCompletion K) → ℂ)
      (Iv : (AdeleRing (𝓞 K) K)ˣ → ℂ),
      AutomorphicForm.IsLocalTestFn K v fv →
      (∀ z, AutomorphicForm.IsOrbitalIntegral K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) fv (Iv z)) →
      Measurable Iv := by
    intro v fv Iv hfv hIv
    obtain ⟨Φv, hΦvlc, hΦv⟩ := hfinplain v fv hfv
    have heq : ∀ z, Iv z = ((cv v : ℝ) : ℂ)⁻¹ * Φv (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
      intro z
      have h := hΦv z (Iv z) (hIv z)
      rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hcv0 v)]
      exact h
    rw [show Iv = fun z => ((cv v : ℝ) : ℂ)⁻¹ * Φv (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)
      from funext heq]
    exact (continuous_const.mul (hΦvlc.continuous.comp (huzc v))).measurable

  refine ⟨?_, ?_, ?_, fun v hv => ⟨?_, ?_, ?_⟩, fun v hv => ?_, fun v hvS hvT => ?_⟩
  ·
    have hIAeq : ∀ z, IA u z = ((N : ℝ) : ℂ)⁻¹ * Φ (pz z) := by
      intro z
      have h := hΦ z (IA u z) (hIA u z hu1)
      rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hN0)]
      exact h
    rw [show (fun z : (AdeleRing (𝓞 K) K)ˣ => IA u z) = fun z => ((N : ℝ) : ℂ)⁻¹ * Φ (pz z) from funext hIAeq]
    exact (continuous_const.mul (hΦs.continuous.comp hpzc)).measurable
  ·
    have hJAeq : ∀ z, JA u z = Ψ (pz z) := fun z => hΨ z _ (hJA u z hu1)
    rw [show (fun z : (AdeleRing (𝓞 K) K)ˣ => JA u z) = fun z => Ψ (pz z) from funext hJAeq]
    exact (hΨc.comp hpzc).measurable
  ·
    have hJA'eq : ∀ z, JA' u z = Ψ' (pz z) := by
      intro z
      by_cases h : ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ
      · exact hΨ' z _ h (hJA' u z hu1 h)
      · rw [hJA'0 u z hu1 h, hΨ'0 z h]
    rw [show (fun z : (AdeleRing (𝓞 K) K)ˣ => JA' u z) = fun z => Ψ' (pz z) from funext hJA'eq]
    exact (hΨ'c.comp hpzc).measurable
  ·
    exact hplainMeas v (fSK v) (fun z => IF u z v) (hfSK v hv) (fun z => hIF u z hu1 v hv)
  ·
    have hJFeq : ∀ z, JF u z v = Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) :=
      fun z => (hΨv v hv).2.2 z _ (hJF u z hu1 v hv)
    rw [show (fun z : (AdeleRing (𝓞 K) K)ˣ => JF u z v) =
        fun z => Ψv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) from funext hJFeq]
    exact ((hΨv v hv).1.continuous.comp (huzc v)).measurable
  ·
    have hJF'eq : ∀ z, JF' u z v = Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
      intro z
      by_cases h : ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ
      · exact (hΨ'v v hv).2.2.1 z _ h (hJF' u z hu1 v hv h)
      · rw [hJF'0 u z hu1 v hv h, (hΨ'v v hv).2.2.2 z h]
    rw [show (fun z : (AdeleRing (𝓞 K) K)ˣ => JF' u z v) =
        fun z => Ψ'v v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) from funext hJF'eq]
    exact ((hΨ'v v hv).1.continuous.comp (huzc v)).measurable
  ·
    exact hplainMeas v (fT v) (fun z => IT u z v) (hfT v hv) (fun z => hIT u z hu1 v hv)
  ·
    exact hplainMeas v ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (fun z => IU u z v) (hind v)
      (fun z => hIU u z hu1 v (fun h => (Finset.mem_union.1 h).elim hvS hvT))

end S_AutomorphicForm_measurable_window_values_of_ne_one_of_prime
end P2MW
export P2MW.S_AutomorphicForm_measurable_window_values_of_ne_one_of_prime (solution)
