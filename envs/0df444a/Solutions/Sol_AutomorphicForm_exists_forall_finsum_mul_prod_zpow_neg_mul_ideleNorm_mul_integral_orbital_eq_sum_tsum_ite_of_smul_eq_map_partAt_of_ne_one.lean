-- Prove2me | solution 1 for AutomorphicForm.exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9d5e2c69-8e65-5ce2-951f-0aaf4fcd7ae2

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
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
import Theorems.Thm_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
import Theorems.Thm_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
import Theorems.Thm_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_pos_of_forall_integral_adelicGLHaar_eq_mul_integral_mul_prod
import Theorems.Thm_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum
import Theorems.Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
import Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units
import Theorems.Thm_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_norm_apply_units_eq_prod_norm_rpow_of_continuous
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport

import Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
import Theorems.Thm_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option maxHeartbeats 1600000 in
open Filter Topology in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNw : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Nw v)
    (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ v)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (κ₀K κK : ℝ)

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
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
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
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v)) :
    ∃ (N : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (sub : Fin N → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (G : Fin N → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) ∧
      ∃ (Rb : ℝ), 0 ≤ Rb ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ k, Rb < |p.1 k|) → G i p = 0) ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G i (p.1, p.2 + Pi.single j 1) = G i p) ∧
      ∃ (x₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : Fin N → Fin T.card → ℤ) (θ₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        ((κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)) *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (AutomorphicForm.SatakeCombination.slotDeg K L ws (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (if h1 : (u : K) - 1 ≠ 0 then
                ((NumberField.TateGlobal.ideleNorm K
                    (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
              else 0) *
            ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
                (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS =
        ∑ i : Fin N, ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            G i (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by

  classical

  obtain ⟨hνA, hcG⟩ :=
    AutomorphicForm.isHaarMeasure_and_pos_of_forall_integral_adelicGLHaar_eq_mul_integral_mul_prod K νA cG hG

  obtain ⟨Φa, hΦa_smooth, hΦa_cs, hΦa_units, ⟨Ca, hCa, hΦa_Ca⟩, hΦa_val⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
      K νZK faK hfaK cτK hcτK νA hνA τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT

  have hR3 : ∀ v ∈ SK, ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      ∀ (u z : (v.adicCompletion K)ˣ), (u : v.adicCompletion K) ≠ 1 →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1)) τ →
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ (fSK v) I →
            (‖(u : v.adicCompletion K) - 1‖ : ℂ) * I = Φ (u, z) := fun v hv =>
    AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
      K v (fSK v) (hfSK v hv)

  have hslot : ∀ v ∈ T, 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v := by
    intro v _hv
    unfold AutomorphicForm.SatakeCombination.slotDeg
    haveI : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
    haveI : ((ws v).1).asIdeal.LiesOver v.asIdeal := by
      refine ⟨?_⟩
      have h : HeightOneSpectrum.under (𝓞 K) (ws v).1 = v := (ws v).2
      exact (congrArg HeightOneSpectrum.asIdeal h).symm
    exact Ideal.inertiaDeg'_pos _ _
  obtain ⟨Λf, Log, hLog, hLog_mul, hΛf_mem, hΛf_disc, hΛf_pf, hΛf_ω⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul K T
      (AutomorphicForm.SatakeCombination.slotDeg K L ws) hslot

  obtain ⟨Λ₁, Log₁, hLog₁, hLog₁_mul, hΛ₁_mem, hΛ₁_disc, hΛ₁_pf, hΛ₁_tors⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T

  obtain ⟨F, hF_T, hF_tors, hF_dec, hF_classes⟩ :=
    NumberField.exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen K T

  let eflip : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) ≃+
      ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    AddEquiv.prodCongr (AddEquiv.refl _) (AddEquiv.neg _)
  let Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    Λf.map eflip.toAddMonoidHom
  have hΛ_mem : ∀ γ, γ ∈ Λ ↔ (γ.1, -γ.2) ∈ Λf := by
    intro γ
    show γ ∈ Λf.map eflip.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map_equiv]
    rfl
  have hΛ_disc : DiscreteTopology Λ := by
    haveI := hΛf_disc
    refine DiscreteTopology.of_continuous_injective
      (f := fun y : Λ => (⟨(y.1.1, -y.1.2), (hΛ_mem _).1 y.2⟩ : Λf))
      ((continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.neg).subtype_mk _) ?_
    intro a b h
    have h' := congrArg Subtype.val h
    simp only [Prod.mk.injEq, neg_inj] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  let ω : Fin T.card → ℝ := fun j => Real.log (Nw (T.equivFin.symm j).1 : ℝ)
  have hω : ω ≠ 0 := by
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    intro h
    apply hΛf_ω hTne
    funext j
    have hj : ω j = 0 := congr_fun h j
    have hvT : (T.equivFin.symm j).1 ∈ T := (T.equivFin.symm j).2
    simp only [ω] at hj
    rw [hNwf _ hvT] at hj
    simp only [Pi.zero_apply, neg_eq_zero]
    exact_mod_cast hj
  let sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ :=
    ∑ i, LinearMap.proj i
  have hpf : ∀ γ ∈ Λ, sl γ.1 = ∑ j, ω j * (γ.2 j : ℝ) := by
    intro γ hγ
    have hmem := (hΛ_mem γ).1 hγ
    have hR1 := hΛf_pf _ hmem
    have hsl : sl γ.1 = ∑ i, γ.1 i := by
      simp [sl, LinearMap.sum_apply]
    rw [hsl]
    simp only at hR1
    rw [hR1]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hvT : (T.equivFin.symm j).1 ∈ T := (T.equivFin.symm j).2
    simp only [ω, hNwf _ hvT, Pi.neg_apply, Int.cast_neg, Nat.cast_pow]
    ring

  obtain ⟨P, sgn, arg, hP_smooth, hP_per, hP_mul, hP_norm, hP_inv, hP_sgnarg, hP_bdd⟩ :=
    NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units K

  have hPZc : PZ.c ≠ 0 := PZ.c_pos.ne'

  have zeroExt : ∀ (v : HeightOneSpectrum (𝓞 K)) (Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ),
      IsLocallyConstant Φ → HasCompactSupport Φ →
      ∃ Φf : (v.adicCompletion K) × (v.adicCompletion K) → ℂ,
        IsLocallyConstant Φf ∧ HasCompactSupport Φf ∧ (∀ p, Φf p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
        ∀ u z : (v.adicCompletion K)ˣ, Φf ((u : v.adicCompletion K), (z : v.adicCompletion K)) = Φ (u, z) := by
    intro v Φ hlc hcs
    set Kv := v.adicCompletion K
    let ι : Kvˣ × Kvˣ → Kv × Kv := fun q => ((q.1 : Kv), (q.2 : Kv))
    have hι : Continuous ι := Units.continuous_val.prodMap Units.continuous_val
    have hιinj : Function.Injective ι := fun a b h => by
      simp only [ι, Prod.mk.injEq] at h
      exact Prod.ext (Units.ext h.1) (Units.ext h.2)
    let Φf : Kv × Kv → ℂ := fun p => if h : IsUnit p.1 ∧ IsUnit p.2 then Φ (h.1.unit, h.2.unit) else 0
    have hval : ∀ u z : Kvˣ, Φf ((u : Kv), (z : Kv)) = Φ (u, z) := by
      intro u z
      have h : IsUnit (u : Kv) ∧ IsUnit (z : Kv) := ⟨u.isUnit, z.isUnit⟩
      simp only [Φf, dif_pos h]
      congr 1
      ext <;> simp [IsUnit.unit_spec]
    have hΦfι : ∀ q, Φf (ι q) = Φ q := fun q => hval q.1 q.2

    set Kc : Set (Kv × Kv) := ι '' tsupport Φ
    have hKc : IsCompact Kc := hcs.image hι
    have hzero : ∀ x, x ∉ Kc → Φf x = 0 := by
      intro x hx
      by_cases h : IsUnit x.1 ∧ IsUnit x.2
      · have hx' : x = ι (h.1.unit, h.2.unit) := by
          simp [ι, IsUnit.unit_spec]
        rw [hx', hΦfι]
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hx (hx' ▸ Set.mem_image_of_mem ι hmem)
      · simp only [Φf, dif_neg h]
    refine ⟨Φf, ?_, HasCompactSupport.intro hKc hzero, ?_, hval⟩
    ·
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ Kc
      · obtain ⟨q, hq, rfl⟩ := hx
        have hvalemb : IsOpenEmbedding (Units.val : Kvˣ → Kv) := by
          refine ⟨Units.isEmbedding_val₀, ?_⟩
          have hr : Set.range (Units.val : Kvˣ → Kv) = {x | x ≠ 0} := by
            ext x
            simp only [Set.mem_range, Set.mem_setOf_eq]
            exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
          rw [hr]
          exact isOpen_ne
        have hopen : IsOpenEmbedding ι := hvalemb.prodMap hvalemb
        have h1 : ∀ᶠ q' in nhds q, Φ q' = Φ q := (IsLocallyConstant.iff_eventually_eq Φ).1 hlc q
        rw [← hopen.map_nhds_eq q, Filter.eventually_map]
        filter_upwards [h1] with q' hq'
        rw [hΦfι, hΦfι, hq']
      · have : ∀ᶠ y in nhds x, y ∉ Kc := hKc.isClosed.isOpen_compl.mem_nhds hx
        filter_upwards [this] with y hy
        rw [hzero y hy, hzero x hx]
    · intro p hp
      by_cases h : IsUnit p.1 ∧ IsUnit p.2
      · exact ⟨h.1.ne_zero, h.2.ne_zero⟩
      · simp [Φf, dif_neg h] at hp

  have hA1' : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Φf : (v.adicCompletion K) × (v.adicCompletion K) → ℂ, v ∈ SK →
      (IsLocallyConstant Φf ∧ HasCompactSupport Φf ∧ (∀ p, Φf p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
        ∀ (u z : (v.adicCompletion K)ˣ), (u : v.adicCompletion K) ≠ 1 →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v
                (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1)) τ →
            τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
            ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ (fSK v) I →
              (‖(u : v.adicCompletion K) - 1‖ : ℂ) * I = Φf ((u : v.adicCompletion K), (z : v.adicCompletion K))) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Φ, hΦlc, hΦcs, hΦ⟩ := hR3 v hv
      obtain ⟨Φf, h1, h2, h3, h4⟩ := zeroExt v Φ hΦlc hΦcs
      refine ⟨Φf, fun _ => ⟨h1, h2, h3, ?_⟩⟩
      intro u z hu τ hτ hτ1 I hI
      rw [h4]
      exact hΦ u z hu τ hτ hτ1 I hI
    · exact ⟨0, fun h => absurd h hv⟩
  choose Φf hΦf using hA1'

  have hU : ∃ U : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ,
      (∀ v ∈ SK, IsOpen (U v : Set (v.adicCompletion K)ˣ)) ∧
      (∀ v ∈ SK, ∀ t ∈ U v, ∀ b z : v.adicCompletion K, Φf v (b * (t : v.adicCompletion K), z) = Φf v (b, z)) ∧
      (∀ v ∈ SK, ∀ ξ ∈ Ξ, ∀ t ∈ U v,
        ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) := by
    have hLC : ∀ v ∈ SK, ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧
        ∀ t ∈ U, ∀ b z : v.adicCompletion K, Φf v (b * (t : v.adicCompletion K), z) = Φf v (b, z) :=
      fun v hv =>
        IsDedekindDomain.HeightOneSpectrum.exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
          K v (Φf v) (hΦf v hv).1 (hΦf v hv).2.1 (hΦf v hv).2.2.1

    have hcontLoc : ∀ v : HeightOneSpectrum (𝓞 K),
        Continuous fun t : (v.adicCompletion K)ˣ => Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t) := by
      intro v
      have hfin : Continuous (Units.map (finIncl (𝓞 K) K)) :=
        Continuous.units_map _ (continuous_const.prodMk continuous_id)
      set S : Set (HeightOneSpectrum (𝓞 K)) := {w | w ≠ v} with hSdef
      have hS : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ Filter.principal S := by
        rw [Filter.le_principal_iff, Filter.mem_cofinite]
        have : Sᶜ = {v} := by ext w; simp [hSdef]
        rw [this]; exact Set.finite_singleton v
      let g₀ : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
          (fun w => ((w.adicCompletionIntegers K) : Set (w.adicCompletion K))) (Filter.principal S) :=
        fun x => ⟨Function.update 1 v x, Filter.eventually_principal.2 fun w hw => by
          have hw' : w ≠ v := hw
          show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v x w ∈ _
          rw [Function.update_of_ne hw']
          exact one_mem _⟩
      have hg₀ : Continuous g₀ :=
        RestrictedProduct.continuous_rng_of_principal.2 (continuous_const.update v continuous_id)
      have hg : Continuous (RestrictedProduct.inclusion _ _ hS ∘ g₀) :=
        (RestrictedProduct.continuous_inclusion hS).comp hg₀
      have hval : (Units.val ∘ localUnit (𝓞 K) K v) =
          (RestrictedProduct.inclusion _ _ hS ∘ g₀) ∘ (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
        funext t
        refine RestrictedProduct.ext _ _ (fun w => ?_)
        simp only [Function.comp_apply, RestrictedProduct.inclusion_apply]
        by_cases hw : w = v
        · subst hw
          first
            | rfl
            | (erw [localUnit_apply_self]; first | rfl | simp [g₀] | (change ((t : w.adicCompletion K)) = Function.update _ _ _ _; simp))
            | simp [localUnit, g₀]
        · first
            | rfl
            | (erw [localUnit_apply_of_ne _ _ _ _ hw]; first | rfl | simp [g₀, Function.update_of_ne hw] | (change (1 : w.adicCompletion K) = Function.update _ _ _ _; simp [Function.update_of_ne hw]))
            | simp [localUnit, g₀, Function.update_of_ne hw]
      have hloc : Continuous (localUnit (𝓞 K) K v) := by
        rw [Units.continuous_iff]
        refine ⟨hval ▸ hg.comp Units.continuous_val, ?_⟩
        have h2 : (fun t : (v.adicCompletion K)ˣ => (((localUnit (𝓞 K) K v t)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) :
            FiniteAdeleRing (𝓞 K) K)) = (Units.val ∘ localUnit (𝓞 K) K v) ∘ (fun t => t⁻¹) := by
          funext t; simp [map_inv]
        rw [h2, hval]
        exact (hg.comp Units.continuous_val).comp continuous_inv
      exact hfin.comp hloc

    have hTc : ∀ (v : HeightOneSpectrum (𝓞 K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ), ξ ∈ Ξ →
        ∃ Uξ : Subgroup (v.adicCompletion K)ˣ, IsOpen (Uξ : Set (v.adicCompletion K)ˣ) ∧
          ∀ t ∈ Uξ, ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1 := by
      intro v ξ hξ
      let χ : (v.adicCompletion K)ˣ →* ℂˣ :=
        ξ.comp ((Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* _).symm.toMonoidHom.comp
          ((Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)))
      have hχ : Continuous fun t : (v.adicCompletion K)ˣ => ((χ t : ℂˣ) : ℂ) := (hΞc ξ hξ).comp (hcontLoc v)
      obtain ⟨-, Uξ, hUo, hU1⟩ :=
        IsDedekindDomain.HeightOneSpectrum.norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
          K v χ hχ
      exact ⟨Uξ, hUo, fun t ht => hU1 t ht⟩

    have hLC' : ∀ v : HeightOneSpectrum (𝓞 K), ∃ U₀ : Subgroup (v.adicCompletion K)ˣ, v ∈ SK →
        (IsOpen (U₀ : Set (v.adicCompletion K)ˣ) ∧
          ∀ t ∈ U₀, ∀ b z : v.adicCompletion K, Φf v (b * (t : v.adicCompletion K), z) = Φf v (b, z)) := by
      intro v
      by_cases hv : v ∈ SK
      · obtain ⟨U₀, h⟩ := hLC v hv; exact ⟨U₀, fun _ => h⟩
      · exact ⟨⊤, fun h => absurd h hv⟩
    choose ULC hULC using hLC'
    have hTc' : ∀ (v : HeightOneSpectrum (𝓞 K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ),
        ∃ Uξ : Subgroup (v.adicCompletion K)ˣ, ξ ∈ Ξ →
          (IsOpen (Uξ : Set (v.adicCompletion K)ˣ) ∧
            ∀ t ∈ Uξ, ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) := by
      intro v ξ
      by_cases hξ : ξ ∈ Ξ
      · obtain ⟨Uξ, h⟩ := hTc v ξ hξ; exact ⟨Uξ, fun _ => h⟩
      · exact ⟨⊤, fun h => absurd h hξ⟩
    choose UTc hUTc using hTc'
    refine ⟨fun v => ULC v ⊓ ⨅ ξ ∈ Ξ, UTc v ξ, ?_, ?_, ?_⟩
    · intro v hv
      have hset : ((ULC v ⊓ ⨅ ξ ∈ Ξ, UTc v ξ : Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ) =
          (ULC v : Set (v.adicCompletion K)ˣ) ∩ ⋂ ξ ∈ Ξ, (UTc v ξ : Set (v.adicCompletion K)ˣ) := by
        simp [Subgroup.coe_inf, Subgroup.coe_iInf]
      rw [hset]
      exact (hULC v hv).1.inter (isOpen_biInter_finset fun ξ hξ => (hUTc v ξ hξ).1)
    · intro v hv t ht b z
      exact (hULC v hv).2 t (Subgroup.mem_inf.1 ht).1 b z
    · intro v hv ξ hξ t ht
      have ht' : t ∈ ⨅ ξ ∈ Ξ, UTc v ξ := (Subgroup.mem_inf.1 ht).2
      rw [Subgroup.mem_iInf] at ht'
      have ht'' := ht' ξ
      rw [Subgroup.mem_iInf] at ht''
      exact (hUTc v ξ hξ).2 t (ht'' hξ)
  obtain ⟨U, hUo, hUΦ, hUξ⟩ := hU

  have hTb : ∀ ξ ∈ Ξ, ∃ σ : NumberField.InfinitePlace K → ℝ, ∀ y : (InfiniteAdeleRing K)ˣ,
      ‖((ξ ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
            InfiniteAdeleRing K →* AdeleRing (𝓞 K) K) y, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ =
        ∏ w, ‖(y : InfiniteAdeleRing K) w‖ ^ σ w := by
    intro ξ hξ
    have hcont : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
        InfiniteAdeleRing K →* AdeleRing (𝓞 K) K)) :=
      Continuous.units_map _ (continuous_id.prodMk continuous_const)
    exact NumberField.InfiniteAdeleRing.exists_norm_apply_units_eq_prod_norm_rpow_of_continuous K
      (ξ.comp ((Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* _).symm.toMonoidHom.comp
        (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
          InfiniteAdeleRing K →* AdeleRing (𝓞 K) K))))
      ((hΞc ξ hξ).comp hcont)

  have hST : ∀ v ∈ SK, v ∉ T := fun v hv hvT => Finset.disjoint_left.1 hTS hvT hv
  obtain ⟨nC, cC, hcC, hclass⟩ :=
    hF_classes (fun v => (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) SK hST U hUo

  have hΦa0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' (Prod.snd '' Ca) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hΦa_Ca p (subset_tsupport _ (Function.mem_support.2 hp))
    refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
    rw [hpq]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
  have hR4 := fun (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (hξ : ξ ∈ Ξ) =>
    NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
      K νZK SK ξ (hΞc ξ hξ) Φa hΦa_smooth hΦa_cs (Prod.snd '' Ca) (hCa.image continuous_snd) hΦa0 Φf
      (fun v hv => ⟨(hΦf v hv).1, (hΦf v hv).2.1, (hΦf v hv).2.2.1⟩)

  have hsummand : ∀ u : Kˣ, (u : K) ≠ 1 →
      (if h1 : (u : K) - 1 ≠ 0 then
          ((NumberField.TateGlobal.ideleNorm K
              (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
                (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
        else 0) *
        ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS =
      ((PZ.c⁻¹ : ℝ) : ℂ) * ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
              (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) := by
    intro u hu

    have hIAval : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        ((∏ w : InfinitePlace K,
            ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) * IA u zS =
          Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
              InfiniteAdeleRing.ringEquiv_mixedSpace K
                (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] :=
      fun zS => hΦa_val u hu zS (IA u zS) (hIA u zS hu)

    have hIFval : ∀ (zS : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ SK)
        (uv zv : (v.adicCompletion K)ˣ),
        (uv : v.adicCompletion K) = (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v →
        (zv : v.adicCompletion K) = (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v →
        AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K zS *
              diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) zv * diagUnits2 uv 1 →
        (‖(uv : v.adicCompletion K) - 1‖ : ℂ) * IF u zS v = Φf v ((uv : v.adicCompletion K), (zv : v.adicCompletion K)) := by
      intro zS v hv uv zv huv hzv hElem
      have huv1 : (uv : v.adicCompletion K) ≠ 1 := by
        have hcomp : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
              algebraMap K (v.adicCompletion K) (u : K) := by
          first
            | rfl
            | simp [Units.coe_map, MonoidHom.coe_coe]
        rw [huv, hcomp]
        intro h
        apply hu
        exact (algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one])

      have key : ∀ (γ : GL (Fin 2) (v.adicCompletion K))
          (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ (fSK v) I →
          γ = Matrix.GeneralLinearGroup.scalar (Fin 2) zv * diagUnits2 uv 1 →
          (‖(uv : v.adicCompletion K) - 1‖ : ℂ) * I = Φf v ((uv : v.adicCompletion K), (zv : v.adicCompletion K)) := by
        intro γ τ hτ hτ1 I hI hγ
        subst hγ
        exact (hΦf v hv).2.2.2 uv zv huv1 τ hτ hτ1 I hI
      exact key _ (τF u zS v) (hτF u zS v hu) (hτF1 u zS v hu) (IF u zS v) (hIF u zS hu v hv) hElem

    have hElem : ∀ (zS : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (uv zv : (v.adicCompletion K)ˣ),
        (uv : v.adicCompletion K) = (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v →
        (zv : v.adicCompletion K) = (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v →
        AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K zS *
              diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) zv * diagUnits2 uv 1 := by
      intro zS v uv zv huv hzv
      have h1v : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
        first
          | rfl
          | exact RestrictedProduct.one_apply
          | simp
      have h1v' : ((1 : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
        first
          | rfl
          | exact RestrictedProduct.one_apply
          | simp
      apply Units.ext
      rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, huv, hzv, h1v, h1v', Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : (u : K) - 1 ≠ 0 := sub_ne_zero.2 hu

    have hN : NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (Units.mk0 ((u : K) - 1) h1))) =
        (∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) * ∏ v ∈ SK, ‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ := by
      rw [NumberField.TateGlobal.ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm K SK
        (Units.mk0 ((u : K) - 1) h1)]
      have e1 : ∀ w : InfinitePlace K, (algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1).1 w =
          (algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 w - 1 := fun w => rfl
      have e2 : ∀ v : HeightOneSpectrum (𝓞 K),
          ((algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1).2 : FiniteAdeleRing (𝓞 K) K) v =
            ((algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2 : FiniteAdeleRing (𝓞 K) K) v - 1 := fun v => rfl
      simp only [Units.val_mk0, map_sub, map_one, e1, e2, Units.coe_map, MonoidHom.coe_coe, AdelicLevel.adeleArch_apply]
    have hNpos : 0 < NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (Units.mk0 ((u : K) - 1) h1))) := NumberField.TateGlobal.ideleNorm_pos _
    have hNi0 : ((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) ≠ 0 := by
      have hr : (∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) ≠ 0 := by
        intro h0
        have hp := hNpos
        rw [hN, h0, zero_mul] at hp
        exact lt_irrefl _ hp
      exact_mod_cast hr
    have hNf0 : ∀ v ∈ SK, (‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℂ) ≠ 0 := by
      intro v hv
      have hr : ‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ ≠ 0 := by
        intro h0
        have hp := hNpos
        rw [hN, Finset.prod_eq_zero hv h0, mul_zero] at hp
        exact lt_irrefl _ hp
      exact_mod_cast hr

    have hIA' : ∀ zS : (AdeleRing (𝓞 K) K)ˣ, IA u zS = ((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ)⁻¹ *
        Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
              (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
            InfiniteAdeleRing.ringEquiv_mixedSpace K
              (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] := by
      intro zS
      rw [eq_inv_mul_iff_mul_eq₀ hNi0]
      exact hIAval zS

    have hIF' : ∀ (zS : (AdeleRing (𝓞 K) K)ˣ), ∀ v ∈ SK, IF u zS v = ((‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ)⁻¹ *
        Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
          (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := by
      intro zS v hv
      rw [eq_inv_mul_iff_mul_eq₀ (hNf0 v hv)]
      exact hIFval zS v hv
        (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))
        (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v zS)
        (NumberField.AdeleRing.val_finiteUnitsComponent _ _)
        (NumberField.AdeleRing.val_finiteUnitsComponent _ _)
        (hElem zS v _ _ (NumberField.AdeleRing.val_finiteUnitsComponent _ _)
          (NumberField.AdeleRing.val_finiteUnitsComponent _ _))

    have hIA'' : ∀ zS : (AdeleRing (𝓞 K) K)ˣ, IA u zS = ((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ)⁻¹ *
        Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] :=
      fun zS => hIA' zS
    have hP0 : (∏ v ∈ SK, ((‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 hNf0
    have hint : ∀ ξ ∈ Ξ,
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS) =
        (((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ)⁻¹ * (∏ v ∈ SK, ((‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ))⁻¹) *
          ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
              ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂PZ.νS := by
      intro ξ hξ
      rw [← integral_const_mul]
      congr 1
      funext zS
      rw [hIA'' zS, Finset.prod_congr rfl (fun v hv => hIF' zS v hv), Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      ring
    rw [dif_pos h1, Finset.sum_congr rfl hint, ← Finset.mul_sum, ← mul_assoc]
    have hNC : ((NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ) * (((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ)⁻¹ * (∏ v ∈ SK, ((‖(((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ))⁻¹) = 1 := by
      rw [hN, Complex.ofReal_mul, Complex.ofReal_prod SK, ← mul_inv]
      exact mul_inv_cancel₀ (mul_ne_zero hNi0 hP0)
    rw [hNC, one_mul]

    have hR : ∀ ξ ∈ Ξ,
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
              ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        ((PZ.c : ℝ) : ℂ) * ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
              ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂PZ.νS := by
      intro ξ hξ
      rw [← hPν, integral_smul_measure, ENNReal.toReal_ofReal PZ.c_pos.le, Complex.real_smul]
    have hc : (((PZ.c)⁻¹ : ℝ) : ℂ) * ((PZ.c : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_inv]
      exact inv_mul_cancel₀ (by exact_mod_cast hPZc)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    rw [hR ξ hξ, ← mul_assoc, hc, one_mul]

  obtain ⟨N, Λc, hΛc_disc, slc, ωc, hωc, hpfc, χ, lift, hlift, sub, hsub, G, hG, Rb, hRb, hGsupp, hGper, x₀, n₀, θ₀, hE⟩ :=
    NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
      K νZK Ξ hΞc hΞt SK T hTS hT2 hur (AutomorphicForm.SatakeCombination.slotDeg K L ws) hslot Nw hNwf ζ s hζ hs hx
      Φa hΦa_smooth hΦa_cs hΦa_units Ca hCa hΦa_Ca Φf (fun v hv => ⟨(hΦf v hv).1, (hΦf v hv).2.1, (hΦf v hv).2.2.1⟩)
      ((κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)) ((PZ.c⁻¹ : ℝ) : ℂ)
  refine ⟨N, Λc, hΛc_disc, slc, ωc, hωc, hpfc, χ, lift, hlift, sub, hsub, G, hG, Rb, hRb, hGsupp, hGper, x₀, n₀, θ₀, fun n => ?_⟩
  rw [← hE n]
  congr 1
  refine finsum_mem_congr rfl (fun u hu => ?_)
  rw [mul_assoc, hsummand u (Set.mem_setOf_eq ▸ hu).1]

end S_AutomorphicForm_exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one (solution)
