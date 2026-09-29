-- Prove2me | solution 1 for AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/08a4bbbe-45af-53b4-9ef4-dfd758592ca8

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
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
import Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace Ws1
namespace CuspUnfold

open AutomorphicForm

theorem det_unipotentGL2 {R : Type*} [CommRing R] (u : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 u) = 1 := by
  apply Units.ext
  simp [Matrix.det_fin_two]

theorem integrable_box (K : Type) [Field K] [NumberField K] {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (g : AdelicGL2 (𝓞 K) K) :
    Integrable (fun q : AdeleRing (𝓞 K) K => φ (unipotentGL2 q * g))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hcont : Continuous (fun q : AdeleRing (𝓞 K) K => φ (unipotentGL2 q * g)) :=
    hφ.comp ((AutomorphicForm.CuspidalSpectrum.continuous_unipotentGL2_adele K).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset K
  have hint : IntegrableOn (fun q : AdeleRing (𝓞 K) K => φ (unipotentGL2 q * g)) (adelicBox K) (adelicAddHaar (𝓞 K) K) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.mpr (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K).ne')

theorem cuspBasis_facts (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ isotypicCuspSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ N S Φ) :
    Continuous φ ∧ (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun t => unipotentGL2 t) φ g = 0 := by
  refine Submodule.span_induction
    (p := fun φ _ => Continuous φ ∧ (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun t => unipotentGL2 t) φ g = 0)
    ?_ ?_ ?_ ?_ h
  · intro φ hφ
    have hA := ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (productionPinsOf K D U gen (adelicBox K)).μ
      (productionPinsOf K D U gen (adelicBox K)).Z ξ (productionPinsOf K D U gen (adelicBox K)).D φ).1
      hφ.smoothCusp.1.1).1
    exact ⟨hφ.continuous, fun γ g => hA.left_invariant γ g, fun g => hφ.smoothCusp.1.2 g⟩
  · exact ⟨continuous_const, fun _ _ => rfl, fun g => by simp [constantTerm, constantTermIntegrand]⟩
  · intro u w _ _ hu hw
    refine ⟨hu.1.add hw.1, fun γ g => by simp only [Pi.add_apply, hu.2.1, hw.2.1], fun g => ?_⟩
    have h1 := hu.2.2 g
    have h2 := hw.2.2 g
    unfold constantTerm constantTermIntegrand at h1 h2 ⊢
    simp only [Pi.add_apply]
    rw [integral_add (integrable_box K hu.1 g) (integrable_box K hw.1 g), h1, h2, add_zero]
  · intro c u _ hu
    refine ⟨hu.1.const_smul c, fun γ g => by simp only [Pi.smul_apply, hu.2.1], fun g => ?_⟩
    have h1 := hu.2.2 g
    unfold constantTerm constantTermIntegrand at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, h1, mul_zero]

end Ws1.CuspUnfold

set_option maxHeartbeats 6400000 in
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
      (e : ιE) (j : Fin (nE e)) (s : ℂ) (_hs : (1 / 2 : ℝ) < s.re) (i : ι),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol
    hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE e j s hs i

  by_cases hdat : ∃ d, AutomorphicForm.IsTruncationDatum K α β d
  swap
  · have h0 : AutomorphicForm.canonicalTruncationDomain K α β = ∅ := by
      unfold AutomorphicForm.canonicalTruncationDomain AutomorphicForm.canonicalTruncationData
      rw [dif_neg hdat]
    rw [h0, Measure.restrict_empty, integral_zero_measure]
  obtain ⟨-, -, -, hΦS, hFD⟩ := AutomorphicForm.canonicalTruncationData_spec K hdat
  set S : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hSdef
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  have hΦS' : Φ₀ ⊆ S := hΦS
  have hFD' : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) := hFD

  obtain ⟨hbcont, hbG, hbCT⟩ := Ws1.CuspUnfold.cuspBasis_facts K _ _ _ ξK N SK (cls i) (hb i).2.1

  have hEpe : ∀ g : AdelicGL2 (𝓞 K) K, EE e j s g = AutomorphicForm.pseudoEisenstein K (φE e j s) g := by
    intro g
    rw [AutomorphicForm.pseudoEisenstein_apply]
    exact (hEE e j).2.2.2.2.2.2.2.2.1 s hs g
  have hint : ∫ g in Φ₀, EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in Φ₀, (fun x => conj (b i x)) g * AutomorphicForm.pseudoEisenstein K (φE e j s) g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    congr 1; funext g; rw [hEpe]; ring
  rw [hint]

  have hSm : MeasurableSet S := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  have hSγ : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * x ∈ S ↔ x ∈ S := by
    intro γ x
    simp only [hSdef, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
      AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hSN : ∀ (u : AdeleRing (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K), unipotentGL2 u * x ∈ S ↔ x ∈ S := by
    intro u x
    simp only [hSdef, Set.mem_setOf_eq, map_mul, Ws1.CuspUnfold.det_unipotentGL2, one_mul]
  have hf : Measurable (fun x => conj (b i x)) := (Complex.continuous_conj.comp hbcont).measurable
  have hψc : Continuous (φE e j s) :=
    (hφEjc e j).comp (continuous_const.prodMk continuous_id)
  have hψ : Measurable (φE e j s) := hψc.measurable
  have hfG : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      (fun x => conj (b i x)) (globalPoints (𝓞 K) K γ * x) = (fun x => conj (b i x)) x := by
    intro γ x; simp only [hbG]
  obtain ⟨hψB, hψN⟩ :=
    AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul K hαm
      (μ e) (ν e) (hμic e) (hνic e) s (φE e j s) (hφE e j s)

  have hfin : ∫⁻ x in Φ₀, ‖(fun x => conj (b i x)) x‖ₑ * (‖φE e j s x‖ₑ + ∑' ξ : K,
        ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ∞ := by
    obtain ⟨C₁, A, hC₁, hgrow⟩ :=
      AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
        K α β hα hαβ hαm (μ e) (ν e) (hμ e) (hν e) s hs (φE e j s) (hφE e j s) hψc
    obtain ⟨h₀, hh₀, hfloor, -⟩ :=
      AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
        K α β hα hαβ
    obtain ⟨k, hk⟩ := exists_nat_ge A
    obtain ⟨C₂, hC₂, hdec⟩ :=
      AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
        K α β hα hαβ ξK hξc hξt SK N hN tysK (cls i) (b i) (hb i).2 k

    set M : ℝ := C₂ * C₁ * (h₀ ^ (A - k)) with hM
    have hbound : ∀ x ∈ Φ₀, ‖(fun x => conj (b i x)) x‖ₑ * (‖φE e j s x‖ₑ + ∑' ξ : K,
        ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖ₑ) ≤ ENNReal.ofReal M := by
      intro x hx
      obtain ⟨hsum, hle⟩ := hgrow x hx
      have hHpos : 0 < NumberField.AdelicHeight.adelicHeight K x := lt_of_lt_of_le hh₀ (hfloor x hx)
      have hb1 : ‖conj (b i x)‖ ≤ C₂ * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ k := by
        rw [Complex.norm_conj]; exact hdec x (hΦS' hx)

      have htsum : (‖φE e j s x‖ₑ + ∑' ξ : K,
          ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖ₑ) =
          ENNReal.ofReal (‖φE e j s x‖ + ∑' ξ : K,
            ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖) := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum]
        simp_rw [ofReal_norm]
      rw [htsum, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hH : NumberField.AdelicHeight.adelicHeight K x ^ A * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ k ≤ h₀ ^ (A - k) := by
        rw [inv_pow, ← Real.rpow_natCast, ← div_eq_mul_inv, ← Real.rpow_sub hHpos]
        exact Real.rpow_le_rpow_of_nonpos hh₀ (hfloor x hx) (by linarith)
      calc ‖conj (b i x)‖ * (‖φE e j s x‖ + ∑' ξ : K,
              ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖)
          ≤ (C₂ * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ k) * (C₁ * NumberField.AdelicHeight.adelicHeight K x ^ A) :=
            mul_le_mul hb1 hle (add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _))
              (mul_nonneg hC₂ (pow_nonneg (inv_nonneg.2 hHpos.le) _))
        _ = C₂ * C₁ * (NumberField.AdelicHeight.adelicHeight K x ^ A * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ k) := by ring
        _ ≤ C₂ * C₁ * h₀ ^ (A - k) := mul_le_mul_of_nonneg_left hH (mul_nonneg hC₂ hC₁)
        _ = M := by rw [hM]

    have hΦnull : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
      have := hFD'.nullMeasurableSet
      exact (nullMeasurableSet_restrict_of_subset hΦS').1 this
    have hvol : adelicGLHaar (Fin 2) (𝓞 K) K Φ₀ < ⊤ := by
      have := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ₀ hFD'
      rwa [Set.inter_eq_left.2 hΦS'] at this
    have hae : ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀, x ∈ Φ₀ := ae_restrict_mem₀ hΦnull
    calc ∫⁻ x in Φ₀, ‖(fun x => conj (b i x)) x‖ₑ * (‖φE e j s x‖ₑ + ∑' ξ : K,
            ‖φE e j s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * x)‖ₑ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ ∫⁻ _ in Φ₀, ENNReal.ofReal M ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_mono_ae (hae.mono fun x hx => hbound x hx)
      _ = ENNReal.ofReal M * adelicGLHaar (Fin 2) (𝓞 K) K Φ₀ := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
  obtain ⟨-, -, -, key⟩ :=
    AutomorphicForm.setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
      K S hSm hSγ hSN Φ₀ hΦS' hFD' (fun x => conj (b i x)) (φE e j s) hf hψ hfG hψB hψN hfin
  rw [key]

  have hCT : ∀ y : AdelicGL2 (𝓞 K) K,
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun t => unipotentGL2 t)
        (fun x => conj (b i x)) y = 0 := by
    intro y
    have h1 := hbCT y
    unfold constantTerm constantTermIntegrand at h1 ⊢
    rw [integral_conj, h1, map_zero]
  simp only [hCT, zero_mul]
  have h0 : (S.indicator fun _ : AdelicGL2 (𝓞 K) K => (0 : ℂ)) = fun _ => 0 := by
    funext x; simp [Set.indicator_apply]
  simp [h0]

end S_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half (solution)
