-- Prove2me | solution 1 for AutomorphicForm.integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d2b98ccf-c17a-57be-9917-0c5e0c925ade

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain Topology
open scoped ENNReal

noncomputable section
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in
open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (fS v))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))

    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K S)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v))
    :
    Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (IA zS * ∏ v ∈ S, IF zS v)) PZ.νS := by
  classical

  obtain ⟨Φ, hΦs, hΦc, -, -, hΦ⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
      K νZK u hu1 fa hfa cτK hcτK νA hνA τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT

  have hB : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Φv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      v ∈ S → (IsLocallyConstant Φv ∧ HasCompactSupport Φv ∧
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
          AutomorphicForm.IsOrbitalIntegral K v
              (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) I →
            (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
              Φv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
                NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨Φv, h1, h2, h3⟩ :=
        AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
          K v u hu1 (fS v) (hfS v hv) (fun z => τF z v) (fun z => hτF z v) (fun z => hτF1 z v)
      exact ⟨Φv, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Φv hΦv using hB

  obtain ⟨T, hTc, hTsupp⟩ :=
    AutomorphicForm.exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
      K S u fa hfa fS hfS νA τA τF IA hIA IF hIF

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

  have hIAeq : ∀ z, IA z = ((N : ℝ) : ℂ)⁻¹ * Φ (pz z) := by
    intro z
    have h := hΦ z (IA z) (hIA z)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hN0)]
    exact h
  have hIFeq : ∀ v ∈ S, ∀ z, IF z v = ((cv v : ℝ) : ℂ)⁻¹ *
      Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by
    intro v hv z
    have h := (hΦv v hv).2.2 z (IF z v) (hIF z v hv)
    rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hcv0 v)]
    exact h

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
  set G : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun zS => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (IA zS * ∏ v ∈ S, IF zS v) with hG
  have hGc : Continuous G := by
    have h1 : Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => IA zS := by
      have : (fun zS : (AdeleRing (𝓞 K) K)ˣ => IA zS) = fun zS => ((N : ℝ) : ℂ)⁻¹ * Φ (pz zS) := funext hIAeq
      rw [this]
      exact continuous_const.mul (hΦs.continuous.comp hpzc)
    have h2 : Continuous fun zS : (AdeleRing (𝓞 K) K)ˣ => ∏ v ∈ S, IF zS v := by
      refine continuous_finsetProd S fun v hv => ?_
      have : (fun zS : (AdeleRing (𝓞 K) K)ˣ => IF zS v) =
          fun zS => ((cv v : ℝ) : ℂ)⁻¹ * Φv v (uv v, NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v zS) :=
        funext (hIFeq v hv)
      rw [this]
      exact continuous_const.mul ((hΦv v hv).1.continuous.comp (continuous_const.prodMk (hfucc v)))
    rw [hG]
    exact hξc.mul (h1.mul h2)

  obtain ⟨CA, hCA⟩ := hΦs.continuous.bounded_above_of_compact_support hΦc
  have hCv : ∀ v, ∃ C, v ∈ S → ∀ x, ‖Φv v x‖ ≤ C := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨C, hC⟩ := (hΦv v hv).1.continuous.bounded_above_of_compact_support (hΦv v hv).2.1
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Cv hCv using hCv
  obtain ⟨Cξ, hCξ⟩ := (hTc.image (NumberField.Idele.continuous_partAt K S)).exists_bound_of_continuousOn
    (f := fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc.continuousOn

  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ) with hU
  have hUm : MeasurableSet U := (NumberField.Idele.isOpen_unitIdelesOutside K _).measurableSet
  have hc0 : ENNReal.ofReal PZ.c ≠ 0 := (ENNReal.ofReal_pos.2 PZ.c_pos).ne'
  have hνS : PZ.νS = (ENNReal.ofReal PZ.c)⁻¹ •
      Measure.map (NumberField.Idele.partAt K S) (νZK.restrict U) := by
    rw [hU, ← hPν, smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul]
  show Integrable G PZ.νS
  rw [hνS]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hc0)
  rw [integrable_map_measure hGc.aestronglyMeasurable (NumberField.Idele.continuous_partAt K S).measurable.aemeasurable]

  show IntegrableOn (G ∘ NumberField.Idele.partAt K S) U νZK
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  have hfin : νZK (U ∩ T) ≠ ⊤ := (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hTc.measure_lt_top).ne
  set M : ℝ := Cξ * ((‖((N : ℝ) : ℂ)⁻¹‖ * CA) * ∏ v ∈ S, (‖((cv v : ℝ) : ℂ)⁻¹‖ * Cv v)) with hM
  have hint : IntegrableOn (G ∘ NumberField.Idele.partAt K S) (U ∩ T) νZK := by
    refine Measure.integrableOn_of_bounded hfin
      ((hGc.comp (NumberField.Idele.continuous_partAt K S)).aestronglyMeasurable) (M := M) ?_
    refine ae_restrict_of_forall_mem (hUm.inter hTm) fun z hz => ?_
    set y := NumberField.Idele.partAt K S z with hy
    have hξb : ‖((ξ ⟨y, Subgroup.mem_top y⟩ : ℂˣ) : ℂ)‖ ≤ Cξ := hCξ y ⟨z, hz.2, rfl⟩
    have hCξ0 : 0 ≤ Cξ := le_trans (norm_nonneg _) hξb
    have hCA0 : 0 ≤ CA := le_trans (norm_nonneg _) (hCA (pz y))
    have hAb : ‖IA y‖ ≤ ‖((N : ℝ) : ℂ)⁻¹‖ * CA := by
      rw [hIAeq, norm_mul]
      exact mul_le_mul_of_nonneg_left (hCA _) (norm_nonneg _)
    have hFb : ‖∏ v ∈ S, IF y v‖ ≤ ∏ v ∈ S, (‖((cv v : ℝ) : ℂ)⁻¹‖ * Cv v) := by
      rw [norm_prod]
      refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v hv => ?_
      rw [hIFeq v hv, norm_mul]
      exact mul_le_mul_of_nonneg_left (hCv v hv _) (norm_nonneg _)
    have hP0 : 0 ≤ ‖∏ v ∈ S, IF y v‖ := norm_nonneg _
    show ‖G y‖ ≤ M
    rw [hG, hM]
    dsimp only
    rw [norm_mul, norm_mul]
    refine mul_le_mul hξb (mul_le_mul hAb hFb hP0 (mul_nonneg (norm_nonneg _) hCA0)) ?_ hCξ0
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine hint.of_forall_diff_eq_zero hUm fun z hz => ?_
  obtain ⟨hzU, hzT⟩ := hz
  have hzT' : z ∉ T := fun h => hzT ⟨hzU, h⟩
  simp only [Function.comp_apply, hG]
  by_cases hA : IA (NumberField.Idele.partAt K S z) = 0
  · rw [hA]; simp
  · have : ∃ v ∈ S, IF (NumberField.Idele.partAt K S z) v = 0 := by
      by_contra hcon
      push_neg at hcon
      exact hzT' (hTsupp z (by rw [hU] at hzU; exact hzU) hA hcon)
    obtain ⟨v, hv, hv0⟩ := this
    rw [Finset.prod_eq_zero hv hv0]; simp

end
end S_AutomorphicForm_integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn (solution)
