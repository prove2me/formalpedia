-- Prove2me | solution 1 for AutomorphicForm.analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/797300cd-f1f4-5f2d-b057-27629d904255

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
import Theorems.Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support"
p2m_attr_erase "simp" "RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (e : ιE) (j : Fin (nE e)) (i : ι),
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) (OE e j) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE e j i
  obtain ⟨hOopen, hOpc, hOax, hOhalf, hEan, hNan, hEjc, hNjc, hEsum, hNint⟩ := hEE e j

  obtain ⟨-, -, -, hΦslab, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hΦeq : AutomorphicForm.canonicalTruncationDomain K α β ∩
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} =
      AutomorphicForm.canonicalTruncationDomain K α β := Set.inter_eq_left.mpr hΦslab
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ _ hΦfd
    rwa [hΦeq] at h
  haveI hfinI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
      (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hΦnull : NullMeasurableSet (AutomorphicForm.canonicalTruncationDomain K α β)
      (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (nullMeasurableSet_restrict_of_subset hΦslab).mp hΦfd.nullMeasurableSet
  haveI hBorel := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hae : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)),
      g ∈ AutomorphicForm.canonicalTruncationDomain K α β := ae_restrict_mem₀ hΦnull
  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      K α β hα hαβ

  have hbcont : Continuous (b i) :=
    AutomorphicForm.continuous_of_mem_isotypicCuspSubmodule (Submodule.mem_inf.mp (hb i).2).1

  set F : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun z g =>
    Set.indicator (AutomorphicForm.canonicalTruncationDomain K α β) (fun g => EE e j z g * conj (b i g)) g
    with hFdef
  have hFeq : ∀ z, ∫ g, F z g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
      (AutomorphicForm.canonicalTruncationDomain K α β)) =
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        EE e j z g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro z
    apply integral_congr_ae
    filter_upwards [hae] with g hg
    simp only [hFdef, Set.indicator_of_mem hg]
  have hD : DifferentiableOn ℂ (fun z => ∫ g, F z g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
      (AutomorphicForm.canonicalTruncationDomain K α β))) (OE e j) := by
    refine MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le _ hOopen F
      ?_ ?_ ?_
    ·
      intro z hz
      have hcont : Continuous (fun g => EE e j z g * conj (b i g)) := by
        have h1 : Continuous (fun g : AdelicGL2 (𝓞 K) K => EE e j z g) :=
          hEjc.comp_continuous (Continuous.prodMk_right z) (fun g => ⟨hz, Set.mem_univ _⟩)
        exact h1.mul (Complex.continuous_conj.comp hbcont)
      refine hcont.aestronglyMeasurable.congr ?_
      filter_upwards [hae] with g hg
      simp only [hFdef, Set.indicator_of_mem hg]
    ·
      intro g
      by_cases hg : g ∈ AutomorphicForm.canonicalTruncationDomain K α β
      · simp only [hFdef, Set.indicator_of_mem hg]
        exact (hEan g).differentiableOn.mul_const _
      · simp only [hFdef, Set.indicator_of_notMem hg]
        exact differentiableOn_const 0
    ·
      intro z₀ hz₀
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOopen z₀ hz₀
      have hCc : IsCompact (Metric.closedBall z₀ (r / 2)) := isCompact_closedBall _ _
      have hCO : Metric.closedBall z₀ (r / 2) ⊆ OE e j :=
        (Metric.closedBall_subset_ball (by linarith)).trans hball
      obtain ⟨M, A, hMA⟩ :=
        AutomorphicForm.forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
          K α β hα hαβ hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (φE e j)
          (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) (OE e j) (EE e j) (NE e j)
          (hEE e j) _ hCc hCO
      obtain ⟨Cb, hCb0, hCb⟩ :=
        AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
          K α β hα hαβ ξK hξc hξt SK N hN tysK (cls i) (b i) (hb i).2 ⌈A⌉₊
      refine ⟨r / 2, by positivity, fun _ => |M| * Cb * h₀ ^ (A - (⌈A⌉₊ : ℝ)), integrable_const _, ?_⟩
      intro z hz g
      have hzC : z ∈ Metric.closedBall z₀ (r / 2) := Metric.ball_subset_closedBall hz
      by_cases hg : g ∈ AutomorphicForm.canonicalTruncationDomain K α β
      · simp only [hFdef, Set.indicator_of_mem hg, norm_mul, Complex.norm_conj]
        have hH : 0 < NumberField.AdelicHeight.adelicHeight K g := lt_of_lt_of_le hh₀ (hfloor g hg)
        have hE : ‖EE e j z g‖ ≤ |M| * NumberField.AdelicHeight.adelicHeight K g ^ A :=
          (hMA z hzC g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg hH.le A))
        have hB : ‖b i g‖ ≤ Cb * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ ⌈A⌉₊ :=
          hCb g (hΦslab hg)
        have hpow : NumberField.AdelicHeight.adelicHeight K g ^ A *
            (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ ⌈A⌉₊ =
            NumberField.AdelicHeight.adelicHeight K g ^ (A - (⌈A⌉₊ : ℝ)) := by
          rw [← Real.rpow_natCast, Real.inv_rpow hH.le, ← Real.rpow_neg hH.le, ← Real.rpow_add hH,
            ← sub_eq_add_neg]
        have hle : NumberField.AdelicHeight.adelicHeight K g ^ (A - (⌈A⌉₊ : ℝ)) ≤ h₀ ^ (A - (⌈A⌉₊ : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hh₀ (hfloor g hg) (sub_nonpos.mpr (Nat.le_ceil A))
        calc ‖EE e j z g‖ * ‖b i g‖
            ≤ (|M| * NumberField.AdelicHeight.adelicHeight K g ^ A) *
                (Cb * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ ⌈A⌉₊) :=
              mul_le_mul hE hB (norm_nonneg _) (by positivity)
          _ = |M| * Cb * (NumberField.AdelicHeight.adelicHeight K g ^ A *
                (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ ⌈A⌉₊) := by ring
          _ = |M| * Cb * NumberField.AdelicHeight.adelicHeight K g ^ (A - (⌈A⌉₊ : ℝ)) := by rw [hpow]
          _ ≤ |M| * Cb * h₀ ^ (A - (⌈A⌉₊ : ℝ)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
      · simp only [hFdef, Set.indicator_of_notMem hg, norm_zero]
        positivity
  have hA : AnalyticOnNhd ℂ (fun z => ∫ g, F z g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
      (AutomorphicForm.canonicalTruncationDomain K α β))) (OE e j) := hD.analyticOnNhd hOopen
  have hfun : (fun s : ℂ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (fun z => ∫ g, F z g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (AutomorphicForm.canonicalTruncationDomain K α β))) := funext fun z => (hFeq z).symm
  rw [hfun]
  exact hA

end S_AutomorphicForm_analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
end P2MW
export P2MW.S_AutomorphicForm_analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis (solution)
