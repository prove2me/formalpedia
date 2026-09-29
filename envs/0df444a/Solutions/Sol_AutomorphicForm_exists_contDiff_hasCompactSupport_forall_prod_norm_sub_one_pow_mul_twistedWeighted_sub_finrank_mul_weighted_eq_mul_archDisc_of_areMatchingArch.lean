-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b61ac798-48d5-5765-a505-167cec19674f

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
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
import Theorems.Thm_AutomorphicForm_exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
import Theorems.Thm_AutomorphicForm_WindowedSiegel_sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
import Theorems.Thm_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in
theorem solution
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ]
    [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cτK : ℝ)
    (hcτK : 0 < cτK)
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
    (cT : ℝ)
    (hcT : 0 < cT)
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
    [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ φa faK)
    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K)
    (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0) :
    ∃ (Bd : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
      (Cd Ed : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ),
      (ContDiff ℝ (⊤ : ℕ∞) Bd) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cd w)) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ed w)) ∧
      (HasCompactSupport Bd) ∧ (∀ w, HasCompactSupport (Cd w)) ∧ (∀ w, HasCompactSupport (Ed w)) ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, (Bd p ≠ 0 ∨ ∃ w, Cd w p ≠ 0 ∨ Ed w p ≠ 0) →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ CaD : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact CaD ∧
        (∀ p ∈ tsupport Bd ∪ ⋃ w, (tsupport (Cd w) ∪ tsupport (Ed w)),
      ∃ q ∈ CaD, p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)])) ∧
      ∀ u : Kˣ, (u : K) ≠ 1 → ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        (((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * (JA' u zS - (Module.finrank K L : ℂ) * JA u zS) =
          (((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ *
            (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))]) := by
  classical
  letI mKinf : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI bKinf : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  subst hνA hνA'

  obtain ⟨τ₀, hτ₀⟩ := AutomorphicForm.exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod K νZK cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT

  obtain ⟨B, C, E, hBs, hCs, hEs, hBc, hCc, hEc, hU, hCa, hR2⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact K L σ hgen hprime φa hφa faK hfaK hmatchA τ₀
  refine ⟨B, C, E, hBs, hCs, hEs, hBc, hCc, hEc, hU, hCa, fun u hu zS => ?_⟩

  have hdiag : ∀ zv uv : (InfiniteAdeleRing K)ˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 2) zv * diagUnits2 uv 1 = diagUnits2 (zv * uv) zv := by
    intro zv uv
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  have hat : Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ = Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) zS := by
    rw [map_inv, map_mul, mul_inv_cancel_right]
  have hA : Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) = Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) zS * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) := by
    rw [← map_mul]
  have hE : AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K zS * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) = diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹) := by
    rw [hat, hA, AutomorphicForm.glArch_centralScalar_mul_diagUnits2 K zS (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1, map_one]
    exact hdiag _ _
  have hTval : ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)) := by
    first
      | rfl
      | simp [Units.coe_map, MonoidHom.coe_coe]
  have hAval : ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))) := by
    first
      | rfl
      | simp [Units.coe_map, MonoidHom.coe_coe]
  have hu1 : ((u⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h
    apply hu
    have h' : u = 1 := inv_eq_one.1 (Units.val_eq_one.1 h)
    rw [h', Units.val_one]
  have hTw : ∀ w : InfinitePlace K,
      ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = algebraMap K w.Completion ((u⁻¹ : Kˣ) : K) := by
    intro w
    rw [hTval]
    first
      | rfl
      | simp [AdelicLevel.adeleArch_apply]
  have hTw1 : ∀ w : InfinitePlace K, ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w ≠ 1 := by
    intro w h
    rw [hTw] at h
    exact hu1 ((algebraMap K w.Completion).injective (h.trans (map_one _).symm))
  have hTw0 : ∀ w : InfinitePlace K, ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w ≠ 0 := by
    intro w h
    rw [hTw] at h
    exact (Units.ne_zero _) ((algebraMap K w.Completion).injective (h.trans (map_zero _).symm))
  have h1T : IsUnit ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) := by
    rw [show IsUnit ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ↔
        ∀ w : InfinitePlace K, IsUnit (((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) w) from Pi.isUnit_iff]
    intro w
    refine isUnit_iff_ne_zero.2 ?_
    show (1 : w.Completion) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w ≠ 0
    exact sub_ne_zero.2 (Ne.symm (hTw1 w))
  have hab : IsUnit (((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) := by
    rw [Units.val_mul, ← mul_one_sub]
    exact (Units.isUnit _).mul h1T
  have hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) := by
    rw [AutomorphicForm.isRegularSemisimple_iff]
    have hcalc : Matrix.trace ((diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) ^ 2 -
        4 * Matrix.det ((diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
        (((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ^ 2 := by
      simp [diagUnits2, Matrix.trace_fin_two, Matrix.det_fin_two]
      ring
    rw [hcalc]
    exact hab.pow 2

  have key : ∀ (γ' : GL (Fin 2) (InfiniteAdeleRing K)) (δ' : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      γ' = AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K zS * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) → δ' = δA u zS →
      ∃ τ : Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (InfiniteAdeleRing K)))),
        τ.IsHaarMeasure ∧
        Measure.map
          (fun x : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) τ = τ₀ ∧
        AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
          γ' τ faK (JA u zS) ∧
        ((∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ γ' δ) →
          AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ' = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ' ∧
          ∃ τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ'),
            τ'.IsHaarMeasure ∧ AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ' δ' 1 τ τ' ∧
            AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
              (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
              δ' τ' (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u zS)) ∧
        ((¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ γ' δ) → JA' u zS = 0) := by
    intro γ' δ' h1 h2
    subst h1 h2
    exact ⟨τA u zS, hτA u zS hu, hτ₀ u zS hu, hJA u zS hu,
      fun hex => ⟨hδA u zS hu hex, τA' u zS, hτA' u zS hu, hτA'c u zS hu hex, hJA' u zS hu hex⟩,
      hJA'0 u zS hu⟩
  obtain ⟨τ, hτ, hτpin, hJ, hlift, hnolift⟩ := key (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) (δA u zS) hE.symm rfl

  rw [← AutomorphicForm.WindowedSiegel.sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul K] at hJ
  have hWL : (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) =
      (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2))) :=
    funext fun y => AutomorphicForm.neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log K L y
  have hR2' := hR2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹) hreg τ hτ hτpin (JA u zS) hJ

  have hval : ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) *
      (JA' u zS - (Module.finrank K L : ℂ) * JA u zS) =
      B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by
    by_cases hex : ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) δ
    · obtain ⟨hN, τ', hτ', hcpl, hJ'⟩ := hlift hex
      rw [hWL] at hJ'
      obtain ⟨α, β, hαβ⟩ := AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2 K L σ (InfiniteAdeleRing K) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹) hab (δA u zS) hN
      obtain ⟨τ'', hτ'', hcpl'', hJ''⟩ : ∃ τ'' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β)),
          τ''.IsHaarMeasure ∧ AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) (diagUnits2 α β) 1 τ τ'' ∧
          AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
            (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
            (diagUnits2 α β) τ'' (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u zS) := by
        have key2 : ∀ δ' : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), δ' = δA u zS →
            ∃ τ'' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ'),
              τ''.IsHaarMeasure ∧ AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) δ' 1 τ τ'' ∧
              AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
                (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
                δ' τ'' (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u zS) := by
          intro δ' h
          subst h
          exact ⟨τ', hτ', hcpl, hJ'⟩
        exact key2 _ hαβ.symm
      have hNαβ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) * Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) := by
        rw [← hαβ]; exact hN
      exact hR2'.1 α β hNαβ τ'' hτ'' hcpl'' (JA' u zS) hJ''
    · rw [hnolift hex]
      exact hR2'.2 hex

  rw [hTval, hAval] at hval
  have hNR0 : (((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, ← Ne]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (div_ne_zero ?_ ?_)
    · rw [← hTval, norm_ne_zero_iff, map_sub, map_one, NumberField.AdelicLevel.archEval_apply]
      exact sub_ne_zero.2 (Ne.symm (hTw1 w))
    · rw [← hTval, NumberField.AdelicLevel.archEval_apply]
      exact Real.sqrt_ne_zero'.2 (norm_pos_iff.2 (hTw0 w))
  rw [← hval, mul_assoc, inv_mul_cancel_left₀ hNR0]

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch (solution)
