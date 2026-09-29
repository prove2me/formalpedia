-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b8d92ccf-7189-5f45-b147-7dd0b03f7190

import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
import Theorems.Thm_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt
import Theorems.Thm_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
import Theorems.Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
import Theorems.Thm_AutomorphicForm_table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq
import Theorems.Thm_AutomorphicForm_exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt
import Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
import Theorems.Thm_AutomorphicForm_isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 16000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4AxSigma

open NumberField.TateGlobal AutomorphicForm

section Modulus
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    beta_reduce at this
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

theorem unitsAct_eq_map (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z = Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z :=
  Units.ext rfl

theorem ideleNorm_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L (D.unitsAct σ z) = ideleNorm L z := by
  rw [unitsAct_eq_map]; exact ideleNorm_unitsMap_act K L D σ z

theorem cpowChar_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ))
    (s : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    cpowChar αL hα s (D.unitsAct g z) =
    cpowChar αL hα s z := by
  apply Units.ext
  rw [cpowChar_apply_val, cpowChar_apply_val]
  have h : ((αL (D.unitsAct g z) : ℝˣ) : ℝ) = ((αL z : ℝˣ) : ℝ) := ideleNorm_unitsAct K L D g z
  rw [h]

theorem unitsAct_symm_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ.symm (D.unitsAct σ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, show σ.symm * σ = 1 from mul_eq_one_iff_eq_inv.mpr rfl, map_one,
    MulAut.one_apply]

theorem unitsAct_apply_symm (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ (D.unitsAct σ.symm z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, show σ * σ.symm = 1 from mul_eq_one_iff_eq_inv.mpr rfl, map_one,
    MulAut.one_apply]
end Modulus

section Alpha
variable (L : Type) [Field L] [NumberField L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

theorem isPrincipalTrivial_alpha :
    IsPrincipalTrivial (R := 𝓞 L) (K := L)
      (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits) := by
  intro u
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  apply Units.ext
  show ((distribHaarChar (AdeleRing (𝓞 L) L) (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) : ℝ≥0) : ℝ) = 1
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap L u
  have : Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom u =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u := rfl
  rw [this] at h
  rw [h]; rfl

theorem continuous_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s : ℂ) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
      ((cpowChar αL hα s z : ℂˣ) : ℂ) := by
  simp only [cpowChar_apply_val]
  show Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ideleNorm L z : ℝ) : ℂ) ^ s
  refine Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm L))
    continuous_const fun z => ?_
  exact Complex.ofReal_mem_slitPlane.2 (ideleNorm_pos z)

theorem isIdeleClassChar_mul {χ ψ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 L) L χ)
    (hψ : IsIdeleClassChar (𝓞 L) L ψ) : IsIdeleClassChar (𝓞 L) L (χ * ψ) := by
  intro u; rw [MonoidHom.mul_apply, hχ u, hψ u, one_mul]

theorem isUnitaryChar_mul {χ ψ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 L) L χ)
    (hψ : IsUnitaryChar (𝓞 L) L ψ) : IsUnitaryChar (𝓞 L) L (χ * ψ) := by
  intro z; rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ z, hψ z, one_mul]

theorem continuous_mul_char {χ ψ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ}
    (hχ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ))
    (hψ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ψ z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((χ * ψ) z : ℂˣ) : ℂ) := by
  simp only [MonoidHom.mul_apply, Units.val_mul]; exact hχ.mul hψ

theorem cpowChar_mul_cpowChar_neg (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((cpowChar αL hα s z : ℂˣ) : ℂ) *
    ((cpowChar αL hα (-s) z : ℂˣ) : ℂ) = 1 := by
  rw [cpowChar_apply_val, cpowChar_apply_val, Complex.cpow_neg]
  exact mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (hα z).ne')))

theorem cpowChar_val_add (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s₁ s₂ : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((cpowChar αL hα (s₁ + s₂) z : ℂˣ) : ℂ) =
    ((cpowChar αL hα s₁ z : ℂˣ) : ℂ) *
    ((cpowChar αL hα s₂ z : ℂˣ) : ℂ) := by
  rw [cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val]
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα z).ne')
end Alpha

section Unif
variable {L : Type} [Field L] [NumberField L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

def idl (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ) :
    (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v t)

theorem idl_fst (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ) :
    ((idl L v t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem idl_snd_self (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ) :
    ((idl L v t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v = t := by
  show ((localUnit (𝓞 L) L v t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v = t
  exact localUnit_apply_self (𝓞 L) L v t

theorem idl_snd_of_ne (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ≠ v) : ((idl L v t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = 1 := by
  show ((localUnit (𝓞 L) L v t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w = 1
  exact localUnit_apply_of_ne (𝓞 L) L v t hw

theorem distribHaarChar_idl_of_valued_eq (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ)
    (ht : Valued.v (t : v.adicCompletion L) = WithZero.exp (-1 : ℤ)) :
    ((distribHaarChar (AdeleRing (𝓞 L) L) (idl L v t) : ℝ≥0) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm L (idl L v t)]
  have h1 : ∏ w : InfinitePlace L,
      ‖((idl L v t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [idl_fst, show (1 : InfiniteAdeleRing L) w = 1 from rfl, norm_one, one_pow]
  have h2 : ∏ᶠ u : HeightOneSpectrum (𝓞 L),
      ‖((idl L v t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 u‖ = ‖(t : v.adicCompletion L)‖ := by
    rw [finprod_eq_single _ v fun u hu => by rw [idl_snd_of_ne v t hu, norm_one], idl_snd_self]
  rw [h1, one_mul, h2, NumberField.FinitePlace.norm_def, ht,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv,
    NNReal.coe_natCast]

theorem det_heckeGen (v : HeightOneSpectrum (𝓞 L)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v) = idl L v (uniformizerUnit L v) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![((idl L v (uniformizerUnit L v) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]).det = _
  rw [Matrix.det_diagonal]
  simp

theorem alpha_det_heckeGen (v : HeightOneSpectrum (𝓞 L)) :
    ((αL (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℝˣ) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [det_heckeGen]
  exact distribHaarChar_idl_of_valued_eq v _ (valued_uniformizerUnit L v)

theorem cpowChar_det_heckeGen
    (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ))
    (s : ℂ) (v : HeightOneSpectrum (𝓞 L)) :
    ((cpowChar αL hα s
        (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ) =
      (HeckeEigensystem.cNorm v) ^ (-s) := by
  rw [cpowChar_apply_val, alpha_det_heckeGen]
  have hN0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hN' : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have harg : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [show HeckeEigensystem.cNorm v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) from rfl]
  push_cast
  rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]

theorem cNorm_ne_zero' (v : HeightOneSpectrum (𝓞 L)) : (HeckeEigensystem.cNorm v : ℂ) ≠ 0 :=
  HeckeEigensystem.cNorm_ne_zero v

theorem cNorm_cpow_add (v : HeightOneSpectrum (𝓞 L)) (a b : ℂ) :
    (HeckeEigensystem.cNorm v) ^ (a + b) = (HeckeEigensystem.cNorm v) ^ a * (HeckeEigensystem.cNorm v) ^ b :=
  Complex.cpow_add _ _ (cNorm_ne_zero' v)

theorem cNorm_cpow_neg_sub (v : HeightOneSpectrum (𝓞 L)) (u r : ℝ) :
    (HeckeEigensystem.cNorm v) ^ (-(((u - r : ℝ) : ℂ) * Complex.I)) =
      (HeckeEigensystem.cNorm v) ^ (-((u : ℂ) * Complex.I)) * (HeckeEigensystem.cNorm v) ^ ((r : ℂ) * Complex.I) := by
  rw [← cNorm_cpow_add]; congr 1; push_cast; ring

theorem cNorm_cpow_sub (v : HeightOneSpectrum (𝓞 L)) (u r : ℝ) :
    (HeckeEigensystem.cNorm v) ^ (((u - r : ℝ) : ℂ) * Complex.I) =
      (HeckeEigensystem.cNorm v) ^ ((u : ℂ) * Complex.I) * (HeckeEigensystem.cNorm v) ^ (-((r : ℂ) * Complex.I)) := by
  rw [← cNorm_cpow_add]; congr 1; push_cast; ring

theorem cNorm_cpow_mul_neg (v : HeightOneSpectrum (𝓞 L)) (s : ℂ) :
    (HeckeEigensystem.cNorm v) ^ s * (HeckeEigensystem.cNorm v) ^ (-s) = 1 := by
  rw [← cNorm_cpow_add, add_neg_cancel, Complex.cpow_zero]
end Unif

section Misc
theorem tsum_eq_tsum_subtype_of_eq_zero {ι : Type*} (s : Set ι) (F : ι → ℂ) (hF : ∀ e, e ∉ s → F e = 0) :
    ∑' e, F e = ∑' e : s, F e :=
  (tsum_subtype_eq_of_support_subset (fun e he => by_contra fun hn => he (hF e hn))).symm

theorem integral_comp_sub' (f : ℝ → ℂ) (c : ℝ) : ∫ t, f t = ∫ u, f (u - c) :=
  (MeasureTheory.integral_sub_right_eq_self f c).symm

theorem under_smul_ideal {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (I : Ideal (𝓞 L)) : (σ • I).under (𝓞 K) = I.under (𝓞 K) := by
  ext x
  simp only [Ideal.under, Ideal.mem_comap]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x := by
    apply Subtype.ext
    show σ⁻¹ ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L)
    exact AlgEquiv.commutes σ⁻¹ (x : K)
  rw [this]
end Misc

section Box
variable {L : Type} [Field L] [NumberField L]

theorem isCompact_tableBox (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξv : HeightOneSpectrum (𝓞 L) → ℂ) :
    IsCompact {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w * ξv w ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) * Real.sqrt ‖ξv w‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by
  classical
  let cst : HeightOneSpectrum (𝓞 L) → ℂ := fun w => HeckeEigensystem.cNorm w * ξv w
  let C : HeightOneSpectrum (𝓞 L) → Set (ℂ × ℂ) := fun w =>
    if w ∈ SL then {0} else
      {p : ℂ × ℂ | p.2 = cst w ∧
        ‖p.1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) * Real.sqrt ‖ξv w‖ ∧
        conj p.1 = conj (cst w) / ((‖cst w‖ : ℝ) : ℂ) * p.1}
  have hC : ∀ w, IsCompact (C w) := by
    intro w
    by_cases hw : w ∈ SL
    · simp only [C, if_pos hw]; exact isCompact_singleton
    · simp only [C, if_neg hw]
      apply Metric.isCompact_of_isClosed_isBounded
      · refine IsClosed.inter (isClosed_eq continuous_snd continuous_const) (IsClosed.inter ?_ ?_)
        · exact isClosed_le (continuous_norm.comp continuous_fst) continuous_const
        · exact isClosed_eq (Complex.continuous_conj.comp continuous_fst) (continuous_const.mul continuous_fst)
      · rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ × ℂ)]
        refine ⟨max (((Ideal.absNorm w.asIdeal : ℝ) + 1) * Real.sqrt ‖ξv w‖) ‖cst w‖, fun p hp => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le_max hp.2.1 (by rw [hp.1])
  have heq : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w * ξv w ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) * Real.sqrt ‖ξv w‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} = Set.univ.pi C := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · rintro ⟨h0, h1⟩ w
      by_cases hw : w ∈ SL
      · simp only [C, if_pos hw, Set.mem_singleton_iff]; exact h0 w hw
      · simp only [C, if_neg hw, Set.mem_setOf_eq]
        obtain ⟨h2, h3, h4⟩ := h1 w hw
        refine ⟨h2, h3, ?_⟩
        rw [show cst w = (x w).2 from h2.symm]; exact h4
    · intro h
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have := h w; simp only [C, if_pos hw, Set.mem_singleton_iff] at this; exact this
      · have := h w
        simp only [C, if_neg hw, Set.mem_setOf_eq] at this
        obtain ⟨h2, h3, h4⟩ := this
        refine ⟨h2, h3, ?_⟩
        rw [show (x w).2 = cst w from h2]; exact h4
  rw [heq]
  exact isCompact_univ_pi hC
end Box

end R4AxSigma

end

open AutomorphicForm R4AxSigma in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ))
    (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μE νE : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μE e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (νE e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μE e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (νE e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
        ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μE e z ≠ μE e' z ∨ νE e z ≠ νE e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm s) (etaSnd (νE e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νE e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μE' νE' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μE' → IsUnitaryChar (𝓞 L) L νE' →
        IsIdeleClassChar (𝓞 L) L μE' → IsIdeleClassChar (𝓞 L) L νE' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ((μE' z : ℂˣ) : ℂ) * ((νE' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μE' αm hαm ((t : ℂ) * Complex.I)) (etaSnd νE' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = μE' z ∧ νE e z = νE' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (κ : ℝ),
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        ∀ (I : ℝ → ℂ) (R₂ : ℝ),
          (∀ R : ℝ, R₂ ≤ R →
            I R = (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
              (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
                    (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
                  conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
                (∫ x in Φ₀,
                  (@AutomorphicForm.lambdaT _
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                    (fun t => AutomorphicForm.unipotentGL2 t)
                    (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                    (EE e i ((t : ℂ) * Complex.I))
                    x) *
                  conj (@AutomorphicForm.lambdaT _
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                    (fun t => AutomorphicForm.unipotentGL2 t)
                    (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                    (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                    x)
                  ∂(adelicGLHaar (Fin 2) (𝓞 L) L))) →
        Summable (fun n : ℕ => cs n * g ⟨tabs n, htabs n⟩) ∧
        Filter.Tendsto (fun R : ℝ => I R - ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g))
          Filter.atTop (nhds 0) := by
  intro αm hαm ιE _iC μE νE _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc
    _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE κ
  classical
  haveI := _iC

  set Xb : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ) :=
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
      (∀ w ∈ SL, x w = 0) ∧
      ∀ w ∉ SL,
      (x w).2 = HeckeEigensystem.cNorm w *
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
      ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
      Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
      ℂˣ) : ℂ)‖ ∧
      conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} with hXb_def
  have hXbX : Xb ⊆ X := hX
  have hXbc : IsCompact Xb := isCompact_tableBox SL _
  let x₀ : HeightOneSpectrum (𝓞 L) → ℂ × ℂ := fun pl => if pl ∈ SL then 0 else
    ((0 : ℂ), HeckeEigensystem.cNorm pl *
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L pl), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
  have hx₀ : x₀ ∈ Xb := by
    refine ⟨fun pl hpl => by simp only [x₀, if_pos hpl], fun pl hpl => ⟨?_, ?_, ?_⟩⟩
    · simp only [x₀, if_neg hpl]
    · simp only [x₀, if_neg hpl, norm_zero]; positivity
    · simp only [x₀, if_neg hpl, map_zero, mul_zero]
  have hXb0 : Xb.Nonempty := ⟨x₀, hx₀⟩

  have hσσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ (D.unitsAct σ.symm z) = z := unitsAct_apply_symm K L D σ
  have hσσ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ.symm (D.unitsAct σ z) = z := unitsAct_symm_apply K L D σ
  have hcpσ : ∀ (s : ℂ) (g : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ), cpowChar αm hαm s (D.unitsAct g z) = cpowChar αm hαm s z :=
    fun s g z => cpowChar_unitsAct K L D g hαm s z
  have hcpdet : ∀ (s : ℂ) (v : HeightOneSpectrum (𝓞 L)),
      ((cpowChar αm hαm s (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ) =
        (HeckeEigensystem.cNorm v) ^ (-s) := fun s v => cpowChar_det_heckeGen hαm s v
  have hnormσ : ∀ (g : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ),
      NumberField.TateGlobal.ideleNorm L (D.unitsAct g z) = NumberField.TateGlobal.ideleNorm L z :=
    fun g z => ideleNorm_unitsAct K L D g z
  have hprod_inv : ∀ e : ιE, (∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ((μE e (D.unitsAct σ.symm z) : ℂˣ) : ℂ) * ((νE e (D.unitsAct σ.symm z) : ℂˣ) : ℂ) =
        ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ)) →
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨z, Subgroup.mem_top z⟩ := by
    intro e h z
    have h1 := _hμν e (D.unitsAct σ.symm z)
    rw [hnormσ, h z, _hμν e z] at h1
    have h2 : ξ' ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩ := by
      rw [hξ', hσσ]
    rw [← h2]
    exact Units.ext h1

  by_cases hdeg : N = ⊥ ∨ (∃ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ ≠ ξL ⟨z, Subgroup.mem_top z⟩) ∨
      ¬ (IsArchTestFactor L φa ∧ ∀ v ∈ S, IsSemiLocalTestFn K L v (φS v))
  · refine ⟨fun _ => x₀, fun _ => hXbX hx₀, fun _ => 0, by simp, fun n hn => absurd rfl hn, ?_⟩
    intro T hTd hT2 hTSL ws w' hw' ϖs hirr hϖs0 ns rTs hcos zs hzs
    refine ⟨0, 0, fun τ₀ ε hε => ⟨fun _ => Set.univ, fun v _ => ⟨isOpen_univ, Set.mem_univ _⟩,
      fun g _ _ => by simpa using hε⟩, ?_⟩
    intro ks js φ hφ hφc φf hfact hbi harch g hg I R₂ hI
    rcases hdeg with hN0 | ⟨z₀, hz₀⟩ | hTF
    ·
      exfalso
      obtain ⟨v, hv⟩ : ∃ v, v ∈ T := Finset.card_pos.mp (by omega)
      have h1 : (ws v).1 ∉ SL := hTSL v hv (ws v).1 (ws v).2
      exact h1 (hN _ (by rw [hN0, Submodule.zero_eq_bot.symm]; exact dvd_zero _))
    ·
      obtain ⟨cMS, hcMS, R₁, HMS⟩ :=
        AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
          K L α β hα hαβ ΦL D σ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ hαm
      have hnotinv : ∀ e : ιE, ∃ z : (AdeleRing (𝓞 L) L)ˣ,
          μE e (D.unitsAct σ.symm z) ≠ μE e z ∨ νE e (D.unitsAct σ.symm z) ≠ νE e z := by
        intro e
        by_contra hcon
        push Not at hcon
        apply hz₀
        refine hprod_inv e (fun z => ?_) z₀
        rw [(hcon z).1, (hcon z).2]
      have hnoC : ∀ (e : ιE) (τ : ℝ), ¬ ((∀ z : (AdeleRing (𝓞 L) L)ˣ,
            μE e (D.unitsAct σ.symm z) = νE e z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            νE e (D.unitsAct σ.symm z) = μE e z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z)) := by
        rintro e τ ⟨h1, h2⟩
        apply hz₀
        refine hprod_inv e (fun z => ?_) z₀
        rw [h1 z, h2 z, Units.val_mul, Units.val_mul]
        have := cpowChar_mul_cpowChar_neg L hαm ((τ : ℂ) * Complex.I) z
        linear_combination ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) * this
      have hzero : ∀ R : ℝ, max R₂ R₁ ≤ R → I R = 0 := by
        intro R hR
        rw [hI R (le_trans (le_max_left _ _) hR)]
        have hR₁ : R₁ ≤ R := le_trans (le_max_right _ _) hR
        have hG : ∀ (e : ιE) (t : ℝ) (i j : Fin (nE e)), _ := fun e t i j =>
          ((HMS (μE e) (νE e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
            (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i)
            (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j)
            (OE e i) (EE e i) (NE e i) (_hEE e i) (OE e j) (EE e j) (NE e j) (_hEE e j) t R hR₁).2.2.2.1
            (hnotinv e) (hnoC e))
        simp only [hG, mul_zero, Finset.sum_const_zero, integral_zero, tsum_zero]
      refine ⟨by simpa using summable_zero, ?_⟩
      simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_add, add_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop (max R₂ R₁)] with R hR
      rw [hzero R hR]; simp
    · exfalso
      refine hTF ⟨hfact.1, fun v hv => ?_⟩
      have hvT : v ∉ T := fun hvT => Finset.disjoint_left.mp hTd hvT hv
      have h := hfact.2.2.1 v (Finset.mem_union_left T hv)
      simp only [if_neg hvT] at h
      exact h

  push Not at hdeg
  obtain ⟨hN0, hξL, hTF⟩ := hdeg
  obtain ⟨φ₀, φf₀, hφ₀c, hφ₀s, hφ₀F, hφ₀T⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
      K L S φa hTF.1 φS hTF.2
  obtain ⟨cMS, hcMS, R₁, HMS⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
      K L α β hα hαβ ΦL D σ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ hαm
  have HADJ := AutomorphicForm.integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
      K L D σ N hN0 hαm
  let a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ₀ (k : AdelicGL2 (𝓞 L) L) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L))
  let Pσ : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℂ := fun e i j =>
    (∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
  let Qσ : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => NE e j s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
  let Uσ : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    (∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
  let Vσ : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (φE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
  obtain ⟨hac, hQc, hUc, hVc, hai, haQ, haU, haV, Lb, hLb, hL1, hL0, hLip⟩ :=
    AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
      K L D σ N tysL S φa φS w ξ' hαm ιE μE νE _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK
      _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE φ₀ hφ₀c hφ₀s φf₀ hφ₀F
  have hLb0 : ∀ e, 0 ≤ Lb e := fun e =>
    le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity) (hL0 e 0)

  let invA : ιE → Prop := fun e =>
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, μE e (D.unitsAct σ.symm z) = μE e z) ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, νE e (D.unitsAct σ.symm z) = νE e z)
  let Csh : ιE → ℝ → Prop := fun e τ =>
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, μE e (D.unitsAct σ.symm z) = νE e z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, νE e (D.unitsAct σ.symm z) = μE e z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z)
  let isC : ιE → Prop := fun e => ¬ invA e ∧ ∃ τ, Csh e τ
  let dg : ιE → Prop := fun e => invA e ∧ ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = νE e z
  have hθex : ∀ e, dg e → ∃ θ : ℝ, ∀ z : (AdeleRing (𝓞 L) L)ˣ, μE e z = νE e z * cpowChar αm hαm ((θ : ℂ) * Complex.I) z := by
    intro e he
    have hcont : Continuous (μE e * (νE e)⁻¹ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun z => (((μE e * (νE e)⁻¹) z : ℂˣ) : ℂ)
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
        exact (_hμc e).mul ((_hνc e).inv₀ fun z => Units.ne_zero _)
      · show Continuous fun z => ((((μE e * (νE e)⁻¹) z)⁻¹ : ℂˣ) : ℂ)
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv, Units.val_mul,
          Units.val_inv_eq_inv_val]
        exact (_hνc e).mul ((_hμc e).inv₀ fun z => Units.ne_zero _)
    have hunit : IsUnitaryChar (𝓞 L) L (μE e * (νE e)⁻¹) := by
      intro z
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
        norm_inv, _hμ e z, _hν e z, inv_one, mul_one]
    have hone : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, (μE e * (νE e)⁻¹) z = 1 := by
      intro z hz
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, he.2 z hz, mul_inv_cancel]
    obtain ⟨θ, hθ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles L _ hcont hunit hone
    refine ⟨θ, fun z => ?_⟩
    have h1 : μE e z * (νE e z)⁻¹ = NumberField.TateGlobal.normPowChar L θ z := by
      have := congrArg (fun χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ => χ z) hθ
      simpa only [MonoidHom.mul_apply, MonoidHom.inv_apply] using this
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [h1, mul_comm]
    congr 1
    apply Units.ext
    rw [cpowChar_apply_val]
    show ((NumberField.TateGlobal.ideleNorm L z : ℝ) : ℂ) ^ (Complex.I * θ) = _
    rw [mul_comm Complex.I]
    rfl

  let θA : ιE → ℝ := fun e => if h : dg e then Classical.choose (hθex e h) else 0
  have hθA : ∀ e, dg e → ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      μE e z = νE e z * cpowChar αm hαm ((θA e : ℂ) * Complex.I) z := by
    intro e h z; simp only [θA, dif_pos h]; exact Classical.choose_spec (hθex e h) z
  let τC : ιE → ℝ := fun e => if h : isC e then Classical.choose h.2 else 0
  have hτC : ∀ e, isC e → Csh e (τC e) := by
    intro e h; simp only [τC, dif_pos h]; exact Classical.choose_spec h.2
  let sh : ιE → ℝ := fun e => if dg e then θA e / 2 else if isC e then τC e / 2 else 0
  let μ₀ : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := fun e =>
    if dg e then μE e * cpowChar αm hαm (-((((θA e / 2 : ℝ)) : ℂ) * Complex.I))
    else if isC e then νE e * cpowChar αm hαm ((((τC e / 2 : ℝ)) : ℂ) * Complex.I) else μE e
  let ν₀ : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ) := fun e =>
    if dg e then νE e * cpowChar αm hαm ((((θA e / 2 : ℝ)) : ℂ) * Complex.I)
    else if isC e then μE e * cpowChar αm hαm (-((((τC e / 2 : ℝ)) : ℂ) * Complex.I)) else νE e
  have hdg_inv : ∀ e, dg e → invA e := fun e h => h.1
  have hC_ninv : ∀ e, isC e → ¬ invA e := fun e h => h.1
  have hdg_nC : ∀ e, dg e → ¬ isC e := fun e h hc => hc.1 h.1
  have hprin : IsPrincipalTrivial (R := 𝓞 L) (K := L) αm := isPrincipalTrivial_alpha L
  have htw_u : ∀ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (r : ℝ), IsUnitaryChar (𝓞 L) L χ →
      IsUnitaryChar (𝓞 L) L (χ * cpowChar αm hαm ((r : ℂ) * Complex.I)) ∧
      IsUnitaryChar (𝓞 L) L (χ * cpowChar αm hαm (-((r : ℂ) * Complex.I))) := by
    intro χ r hχ
    exact ⟨isUnitaryChar_mul L hχ (cpowChar_isUnitaryChar_of_re_eq_zero (by simp)),
      isUnitaryChar_mul L hχ (cpowChar_isUnitaryChar_of_re_eq_zero (by simp))⟩
  have htw_ic : ∀ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (s : ℂ), IsIdeleClassChar (𝓞 L) L χ →
      IsIdeleClassChar (𝓞 L) L (χ * cpowChar αm hαm s) := fun χ s hχ =>
    isIdeleClassChar_mul L hχ (cpowChar_isIdeleClassChar hprin s)
  have htw_c : ∀ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (s : ℂ),
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)) →
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (((χ * cpowChar αm hαm s) z : ℂˣ) : ℂ) := fun χ s hχ =>
    continuous_mul_char L hχ (continuous_cpowChar L hαm s)
  have hunrE : ∀ (e : ιE) (i : Fin (nE e)) (pl : HeightOneSpectrum (𝓞 L)), pl ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt (μE e) pl ∧ NumberField.TateGlobal.IsUnramifiedCharAt (νE e) pl := by
    intro e i pl hpl
    have hplN : ¬ pl.asIdeal ∣ N := fun h => hpl (hN pl h)
    have hφ0 : φE e i 0 ≠ 0 := by
      intro h0
      have h1 := _hφEon e i i
      rw [if_pos rfl, h0] at h1
      simp at h1
    exact AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel L N hαm
      (μE e) (νE e) 0 (φE e i 0) (_hφE e i 0) hφ0 (_hφElev e i 0) pl hplN
  have htw_unr : ∀ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (s : ℂ) (pl : HeightOneSpectrum (𝓞 L)),
      NumberField.TateGlobal.IsUnramifiedCharAt χ pl →
      NumberField.TateGlobal.IsUnramifiedCharAt (χ * cpowChar αm hαm s) pl := fun χ s pl h =>
    AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt L hαm χ s pl h
  have hμ₀u : ∀ e, IsUnitaryChar (𝓞 L) L (μ₀ e) := by
    intro e
    by_cases hd : dg e
    · simp only [μ₀, if_pos hd]; exact (htw_u _ _ (_hμ e)).2
    by_cases hc : isC e
    · simp only [μ₀, if_neg hd, if_pos hc]; exact (htw_u _ _ (_hν e)).1
    · simp only [μ₀, if_neg hd, if_neg hc]; exact _hμ e
  have hν₀u : ∀ e, IsUnitaryChar (𝓞 L) L (ν₀ e) := by
    intro e
    by_cases hd : dg e
    · simp only [ν₀, if_pos hd]; exact (htw_u _ _ (_hν e)).1
    by_cases hc : isC e
    · simp only [ν₀, if_neg hd, if_pos hc]; exact (htw_u _ _ (_hμ e)).2
    · simp only [ν₀, if_neg hd, if_neg hc]; exact _hν e
  have hμ₀ic : ∀ e, IsIdeleClassChar (𝓞 L) L (μ₀ e) := by
    intro e
    by_cases hd : dg e
    · simp only [μ₀, if_pos hd]; exact htw_ic _ _ (_hμic e)
    by_cases hc : isC e
    · simp only [μ₀, if_neg hd, if_pos hc]; exact htw_ic _ _ (_hνic e)
    · simp only [μ₀, if_neg hd, if_neg hc]; exact _hμic e
  have hν₀ic : ∀ e, IsIdeleClassChar (𝓞 L) L (ν₀ e) := by
    intro e
    by_cases hd : dg e
    · simp only [ν₀, if_pos hd]; exact htw_ic _ _ (_hνic e)
    by_cases hc : isC e
    · simp only [ν₀, if_neg hd, if_pos hc]; exact htw_ic _ _ (_hμic e)
    · simp only [ν₀, if_neg hd, if_neg hc]; exact _hνic e
  have hμ₀c : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ₀ e z : ℂˣ) : ℂ) := by
    intro e
    by_cases hd : dg e
    · simp only [μ₀, if_pos hd]; exact htw_c _ _ (_hμc e)
    by_cases hc : isC e
    · simp only [μ₀, if_neg hd, if_pos hc]; exact htw_c _ _ (_hνc e)
    · simp only [μ₀, if_neg hd, if_neg hc]; exact _hμc e
  have hν₀c : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν₀ e z : ℂˣ) : ℂ) := by
    intro e
    by_cases hd : dg e
    · simp only [ν₀, if_pos hd]; exact htw_c _ _ (_hνc e)
    by_cases hc : isC e
    · simp only [ν₀, if_neg hd, if_pos hc]; exact htw_c _ _ (_hμc e)
    · simp only [ν₀, if_neg hd, if_neg hc]; exact _hνc e
  have hμν₀ : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
      ((μ₀ e z : ℂˣ) : ℂ) * ((ν₀ e z : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro e z
    rw [← _hμν e z]
    by_cases hd : dg e
    · simp only [μ₀, ν₀, if_pos hd, MonoidHom.mul_apply, Units.val_mul]
      have := cpowChar_mul_cpowChar_neg L hαm ((((θA e / 2 : ℝ)) : ℂ) * Complex.I) z
      linear_combination ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) * this
    by_cases hc : isC e
    · simp only [μ₀, ν₀, if_neg hd, if_pos hc, MonoidHom.mul_apply, Units.val_mul]
      have := cpowChar_mul_cpowChar_neg L hαm ((((τC e / 2 : ℝ)) : ℂ) * Complex.I) z
      linear_combination ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) * this
    · simp only [μ₀, ν₀, if_neg hd, if_neg hc]
  have hinv_fwd : ∀ e, invA e → ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      μE e (D.unitsAct σ z) = μE e z ∧ νE e (D.unitsAct σ z) = νE e z := by
    intro e h z
    have h1 := h.1 (D.unitsAct σ z); have h2 := h.2 (D.unitsAct σ z)
    rw [hσσ'] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  have hcpow_inv_val : ∀ (s : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
      (((cpowChar αm hαm s z)⁻¹ : ℂˣ) : ℂ) = ((cpowChar αm hαm (-s) z : ℂˣ) : ℂ) := by
    intro s z
    rw [Units.val_inv_eq_inv_val]
    have := cpowChar_mul_cpowChar_neg L hαm s z
    exact (eq_inv_of_mul_eq_one_right this).symm ▸ rfl
  have hC_fwd : ∀ e, isC e → ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ((μE e (D.unitsAct σ z) : ℂˣ) : ℂ) = ((νE e z : ℂˣ) : ℂ) * ((cpowChar αm hαm ((τC e : ℂ) * Complex.I) z : ℂˣ) : ℂ) ∧
      ((νE e (D.unitsAct σ z) : ℂˣ) : ℂ) = ((μE e z : ℂˣ) : ℂ) * ((cpowChar αm hαm (-((τC e : ℂ) * Complex.I)) z : ℂˣ) : ℂ) := by
    intro e h z
    obtain ⟨h1, h2⟩ := hτC e h
    have h1' := h1 (D.unitsAct σ z); have h2' := h2 (D.unitsAct σ z)
    rw [hσσ', hcpσ] at h1' h2'
    have e1 := congrArg (fun x : ℂˣ => (x : ℂ)) h1'
    have e2 := congrArg (fun x : ℂˣ => (x : ℂ)) h2'
    simp only [Units.val_mul] at e1 e2
    have hcc := cpowChar_mul_cpowChar_neg L hαm ((τC e : ℂ) * Complex.I) z
    constructor
    ·
      linear_combination -((cpowChar αm hαm ((τC e : ℂ) * Complex.I) z : ℂˣ) : ℂ) * e2 -
        ((μE e (D.unitsAct σ z) : ℂˣ) : ℂ) * hcc
    · linear_combination -((cpowChar αm hαm (-((τC e : ℂ) * Complex.I)) z : ℂˣ) : ℂ) * e1 -
        ((νE e (D.unitsAct σ z) : ℂˣ) : ℂ) * hcc
  have hrel : ∀ e, (invA e ∨ isC e) →
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (D.unitsAct σ z) = (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) z ∧
        (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (D.unitsAct σ z) = (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) z) ∨
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (D.unitsAct σ z) = (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) z ∧
        (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (D.unitsAct σ z) = (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) z) := by
    intro e he
    by_cases hd : dg e
    · left
      intro z
      obtain ⟨h1, h2⟩ := hinv_fwd e hd.1 z
      refine ⟨?_, ?_⟩ <;> simp only [μ₀, ν₀, if_pos hd, MonoidHom.mul_apply, hcpσ, h1, h2]
    rcases he with hA | hc
    · left
      intro z
      have hnc : ¬ isC e := fun hc => hc.1 hA
      obtain ⟨h1, h2⟩ := hinv_fwd e hA z
      refine ⟨?_, ?_⟩ <;> simp only [μ₀, ν₀, if_neg hd, if_neg hnc, MonoidHom.mul_apply, hcpσ, h1, h2]
    · right
      intro z
      obtain ⟨e1, e2⟩ := hC_fwd e hc z
      simp only [μ₀, ν₀, if_neg hd, if_pos hc, MonoidHom.mul_apply, hcpσ]
      have hadd1 := cpowChar_val_add L hαm ((τC e : ℂ) * Complex.I) (-((((τC e / 2 : ℝ)) : ℂ) * Complex.I)) z
      have hadd2 := cpowChar_val_add L hαm (-((τC e : ℂ) * Complex.I)) ((((τC e / 2 : ℝ)) : ℂ) * Complex.I) z
      have hex1 : (τC e : ℂ) * Complex.I + -((((τC e / 2 : ℝ)) : ℂ) * Complex.I) = (((τC e / 2 : ℝ)) : ℂ) * Complex.I := by
        push_cast; ring
      have hex2 : -((τC e : ℂ) * Complex.I) + (((τC e / 2 : ℝ)) : ℂ) * Complex.I = -((((τC e / 2 : ℝ)) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hex1] at hadd1; rw [hex2] at hadd2
      constructor
      · apply Units.ext
        simp only [Units.val_mul]
        rw [e2]
        linear_combination -(((μE e z : ℂˣ) : ℂ) * ((cpowChar αm hαm (((w / 2 : ℝ) : ℂ)) z : ℂˣ) : ℂ)) * hadd2
      · apply Units.ext
        simp only [Units.val_mul]
        rw [e1]
        linear_combination -(((νE e z : ℂˣ) : ℂ) * ((cpowChar αm hαm (((w / 2 : ℝ) : ℂ)) z : ℂˣ) : ℂ)) * hadd1
  have hur₀ : ∀ (e : ιE) (i : Fin (nE e)) (pl : HeightOneSpectrum (𝓞 L)), pl ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) pl ∧
      NumberField.TateGlobal.IsUnramifiedCharAt (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) pl := by
    intro e i pl hpl
    obtain ⟨h1, h2⟩ := hunrE e i pl hpl
    by_cases hd : dg e
    · simp only [μ₀, ν₀, if_pos hd]
      exact ⟨htw_unr _ _ _ (htw_unr _ _ _ h1), htw_unr _ _ _ (htw_unr _ _ _ h2)⟩
    by_cases hc : isC e
    · simp only [μ₀, ν₀, if_neg hd, if_pos hc]
      exact ⟨htw_unr _ _ _ (htw_unr _ _ _ h2), htw_unr _ _ _ (htw_unr _ _ _ h1)⟩
    · simp only [μ₀, ν₀, if_neg hd, if_neg hc]
      exact ⟨htw_unr _ _ _ h1, htw_unr _ _ _ h2⟩
  have hur₀' : ∀ (e : ιE) (i : Fin (nE e)) (pl : HeightOneSpectrum (𝓞 L)), pl ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt (μ₀ e) pl ∧ NumberField.TateGlobal.IsUnramifiedCharAt (ν₀ e) pl := by
    intro e i pl hpl
    obtain ⟨h1, h2⟩ := hunrE e i pl hpl
    by_cases hd : dg e
    · simp only [μ₀, ν₀, if_pos hd]; exact ⟨htw_unr _ _ _ h1, htw_unr _ _ _ h2⟩
    by_cases hc : isC e
    · simp only [μ₀, ν₀, if_neg hd, if_pos hc]; exact ⟨htw_unr _ _ _ h2, htw_unr _ _ _ h1⟩
    · simp only [μ₀, ν₀, if_neg hd, if_neg hc]; exact ⟨h1, h2⟩

  let Sset : Set ιE := {e | invA e ∨ isC e}
  let AP : Sset → HeightOneSpectrum (𝓞 L) → ℂ := fun e v =>
    (((μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ)
  let BP : Sset → HeightOneSpectrum (𝓞 L) → ℂ := fun e v =>
    (((ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ)
  let M₀ : HeightOneSpectrum (𝓞 L) → ℝ := fun v =>
    ‖((cpowChar αm hαm (((w / 2 : ℝ) : ℂ)) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ)‖
  let τP : Sset → ℝ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ) := fun e u =>
    (fun v : HeightOneSpectrum (𝓞 L) => if v ∈ SL then (0 : ℂ × ℂ) else
      ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          ((((μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ) *
              (HeckeEigensystem.cNorm v) ^ (-((u : ℂ) * Complex.I)) +
            (((ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ) *
              (HeckeEigensystem.cNorm v) ^ ((u : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) *
          (((μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ) *
          (((ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) : ℂˣ) : ℂ)))
  let PP : ∀ e : Sset, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j _ => if invA e then Pσ e i j else 0
  let QP : ∀ e : Sset, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t => if invA e then Qσ e i j (t - sh e) else 0
  let UP : ∀ e : Sset, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    if (dg e ∨ isC e) then Uσ e i j (t - sh e) else 0
  let VP : ∀ e : Sset, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    if (dg e ∨ isC e) then Vσ e i j (t - sh e) else 0
  let aP : ∀ e : Sset, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t => a e i j (t - sh e)
  have hA : ∀ e v, AP e v ≠ 0 := fun e v => Units.ne_zero _
  have hB : ∀ e v, BP e v ≠ 0 := fun e v => Units.ne_zero _
  have hAM : ∀ e v, ‖AP e v‖ ≤ M₀ v := by
    intro e v
    simp only [AP, M₀, MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ₀u e _, one_mul, le_refl]
  have hBM : ∀ e v, ‖BP e v‖ ≤ M₀ v := by
    intro e v
    simp only [BP, M₀, MonoidHom.mul_apply, Units.val_mul, norm_mul, hν₀u e _, one_mul, le_refl]
  have hτ : ∀ (e : Sset) (t : ℝ) (v : HeightOneSpectrum (𝓞 L)), v ∉ SL →
      τP e t v = ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (AP e v * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + BP e v * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) * AP e v * BP e v) := by
    intro e t v hv; simp only [τP, AP, BP, if_neg hv]
  have hτS : ∀ (e : Sset) (t : ℝ) (v : HeightOneSpectrum (𝓞 L)), v ∈ SL → τP e t v = 0 := by
    intro e t v hv; simp only [τP, if_pos hv]
  have hξLv : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := fun z => by rw [hξL z]
  have hτX : ∀ (e : Sset) (t : ℝ), τP e t ∈ Xb := by
    intro e t
    have h := AutomorphicForm.table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq L SL ξ' w hαm
      (μ₀ e) (ν₀ e) (hμ₀u e) (hν₀u e) (hμν₀ e) t
    simp only [hξLv] at h
    exact h
  have hPc : ∀ (e : Sset) i j t, PP e i j t = PP e i j 0 := fun _ _ _ _ => rfl
  have hQc' : ∀ (e : Sset) i j, Continuous (QP e i j) := by
    intro e i j
    by_cases h : invA e
    · simp only [QP, if_pos h]; exact (hQc e i j).comp (continuous_id.sub continuous_const)
    · simp only [QP, if_neg h]; exact continuous_const
  have hUc' : ∀ (e : Sset) i j, Continuous (UP e i j) := by
    intro e i j
    by_cases h : dg e ∨ isC e
    · simp only [UP, if_pos h]; exact (hUc e i j).comp (continuous_id.sub continuous_const)
    · simp only [UP, if_neg h]; exact continuous_const
  have hVc' : ∀ (e : Sset) i j, Continuous (VP e i j) := by
    intro e i j
    by_cases h : dg e ∨ isC e
    · simp only [VP, if_pos h]; exact (hVc e i j).comp (continuous_id.sub continuous_const)
    · simp only [VP, if_neg h]; exact continuous_const
  have hac' : ∀ (e : Sset) i j, Continuous (aP e i j) := fun e i j =>
    (hac e i j).comp (continuous_id.sub continuous_const)
  have hai' : ∀ (e : Sset) i j, Integrable (aP e i j) := fun e i j =>
    (hai e i j).comp_sub_right (sh e)
  have haQ' : ∀ (e : Sset) i j, Integrable (fun t => aP e i j t * QP e i j t) := by
    intro e i j
    by_cases h : invA e
    · simp only [aP, QP, if_pos h]; exact (haQ e i j).comp_sub_right (sh e)
    · simp only [aP, QP, if_neg h, mul_zero]; exact integrable_zero _ _ _
  have haU' : ∀ (e : Sset) i j, Integrable (fun t => aP e i j t * UP e i j t) := by
    intro e i j
    by_cases h : dg e ∨ isC e
    · simp only [aP, UP, if_pos h]; exact (haU e i j).comp_sub_right (sh e)
    · simp only [aP, UP, if_neg h, mul_zero]; exact integrable_zero _ _ _
  have haV' : ∀ (e : Sset) i j, Integrable (fun t => aP e i j t * VP e i j t) := by
    intro e i j
    by_cases h : dg e ∨ isC e
    · simp only [aP, VP, if_pos h]; exact (haV e i j).comp_sub_right (sh e)
    · simp only [aP, VP, if_neg h, mul_zero]; exact integrable_zero _ _ _
  have hUV0σ : ∀ (e : ιE) (i j : Fin (nE e)), (dg e ∨ isC e) → Uσ e i j (0 - sh e) = Vσ e i j (0 - sh e) := by
    intro e i j h
    have HA := HADJ (μE e) (νE e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
      (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i) (_hφElev e i)
      (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j) (_hφElev e j)
      (OE e i) (EE e i) (NE e i) (_hEE e i) (OE e j) (EE e j) (NE e j) (_hEE e j)
    by_cases hd : dg e
    · have h1 := HA.1 hd.1.1 hd.1.2 (θA e) (hθA e hd)
      simp only [sh, if_pos hd, zero_sub, Uσ, Vσ]
      exact h1
    · have hc : isC e := h.resolve_left hd
      obtain ⟨hn, -⟩ := id hc
      have hninv : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
          μE e (D.unitsAct σ.symm z) ≠ μE e z ∨ νE e (D.unitsAct σ.symm z) ≠ νE e z := by
        by_contra hcon; push Not at hcon; exact hn ⟨fun z => (hcon z).1, fun z => (hcon z).2⟩
      have h1 := HA.2 (τC e) (hτC e hc).1 (hτC e hc).2 hninv
      simp only [sh, if_neg hd, if_pos hc, zero_sub, Uσ, Vσ]
      exact h1
  have hUV0 : ∀ (e : Sset) i j, UP e i j 0 = VP e i j 0 := by
    intro e i j
    by_cases h : dg e ∨ isC e
    · simp only [UP, VP, if_pos h]; exact hUV0σ e i j h
    · simp only [UP, VP, if_neg h]
  have hL1' : ∀ e : Sset, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
      ∫ t : ℝ, (‖aP e i j t‖ * (1 + ‖PP e i j t‖) + ‖aP e i j t * QP e i j t‖ +
        ‖aP e i j t * UP e i j t‖ + ‖aP e i j t * VP e i j t‖) ≤ Lb e := by
    intro e
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) (hL1 e)
    have hfull_int : Integrable (fun t : ℝ => ‖a e i j t‖ * (1 + ‖Pσ e i j‖) + ‖a e i j t * Qσ e i j t‖ +
        ‖a e i j t * Uσ e i j t‖ + ‖a e i j t * Vσ e i j t‖) := by
      refine Integrable.add (Integrable.add (Integrable.add ?_ (haQ e i j).norm) (haU e i j).norm) (haV e i j).norm
      exact (hai e i j).norm.mul_const _
    rw [← MeasureTheory.integral_sub_right_eq_self (fun t : ℝ => ‖a e i j t‖ * (1 + ‖Pσ e i j‖) + ‖a e i j t * Qσ e i j t‖ +
        ‖a e i j t * Uσ e i j t‖ + ‖a e i j t * Vσ e i j t‖) (sh e)]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      (hfull_int.comp_sub_right (sh e)) (Filter.Eventually.of_forall fun t => ?_)
    have h1 : ‖aP e i j t‖ * (1 + ‖PP e i j t‖) ≤ ‖a e i j (t - sh e)‖ * (1 + ‖Pσ e i j‖) := by
      simp only [aP, PP]
      by_cases h : invA e
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h, norm_zero, add_zero, mul_one]
        exact le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _))
    have h2 : ‖aP e i j t * QP e i j t‖ ≤ ‖a e i j (t - sh e) * Qσ e i j (t - sh e)‖ := by
      simp only [aP, QP]
      by_cases h : invA e
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h, mul_zero, norm_zero]; exact norm_nonneg _
    have h3 : ‖aP e i j t * UP e i j t‖ ≤ ‖a e i j (t - sh e) * Uσ e i j (t - sh e)‖ := by
      simp only [aP, UP]
      by_cases h : dg e ∨ isC e
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h, mul_zero, norm_zero]; exact norm_nonneg _
    have h4 : ‖aP e i j t * VP e i j t‖ ≤ ‖a e i j (t - sh e) * Vσ e i j (t - sh e)‖ := by
      simp only [aP, VP]
      by_cases h : dg e ∨ isC e
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h, mul_zero, norm_zero]; exact norm_nonneg _
    linarith
  have hL0' : ∀ e : Sset, ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖aP e i j 0‖ * (‖UP e i j 0‖ + ‖VP e i j 0‖) ≤ Lb e := by
    intro e
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) (hL0 e (0 - sh e))
    simp only [aP, UP, VP]
    by_cases h : dg e ∨ isC e
    · simp only [if_pos h]; exact le_refl _
    · simp only [if_neg h, norm_zero, add_zero, mul_zero]; positivity
  have hLip' : ∀ (e : Sset) (t : ℝ), |t| ≤ 1 →
      (∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ‖aP e i j t * (UP e i j t + VP e i j t) - aP e i j 0 * (UP e i j 0 + VP e i j 0)‖) ≤ Lb e * |t| ∧
      (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖aP e i j t * (UP e i j t - VP e i j t)‖) ≤ Lb e * |t| := by
    intro e t _
    have habs : |t - sh e - (0 - sh e)| = |t| := by congr 1; ring
    obtain ⟨hl1, hl2⟩ := hLip e (t - sh e) (0 - sh e)
    rw [habs] at hl1 hl2
    constructor
    · refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) hl1
      simp only [aP, UP, VP]
      by_cases h : dg e ∨ isC e
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h, add_zero, mul_zero, sub_zero, norm_zero]; exact norm_nonneg _
    · refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) hl2
      simp only [aP, UP, VP]
      by_cases h : dg e ∨ isC e
      · simp only [if_pos h]
        have h0 : a e i j (0 - sh e) * (Uσ e i j (0 - sh e) - Vσ e i j (0 - sh e)) = 0 := by
          rw [hUV0σ e i j h, sub_self, mul_zero]
        have hXY : ‖a e i j (t - sh e) * (Uσ e i j (t - sh e) - Vσ e i j (t - sh e))‖ =
            ‖a e i j (t - sh e) * (Uσ e i j (t - sh e) - Vσ e i j (t - sh e)) -
              a e i j (0 - sh e) * (Uσ e i j (0 - sh e) - Vσ e i j (0 - sh e))‖ := by
          rw [h0, sub_zero]
        rw [hXY]
      · simp only [if_neg h, sub_zero, mul_zero, norm_zero]; exact norm_nonneg _
  obtain ⟨tabs, htabsb, cs, hsum, htabsat, HP⟩ :=
    AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
      L SL Xb hXbc hXb0 Sset (fun e => nE e) AP BP hA hB M₀ hAM hBM τP hτ hτS hτX (κ : ℂ) (cMS : ℂ)
      PP QP UP VP aP hPc hQc' hUc' hVc' hac' hai' haQ' haU' haV' hUV0 (fun e => Lb e) (hLb.subtype _) hL1' hL0' hLip'
  refine ⟨tabs, fun n => hXbX (htabsb n), cs, hsum, ?_, ?_⟩

  · intro n hn
    obtain ⟨e, hne, htn⟩ := htabsat n hn
    have he : invA e ∨ isC e := e.2
    have i₀ : Fin (nE e) := ⟨0, hne⟩
    constructor
    · intro pl pl' hpl hpl' hunder
      rw [htn, hτ e 0 pl hpl, hτ e 0 pl' hpl']
      obtain ⟨hsum', hprod', hq⟩ :=
        AutomorphicForm.apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
          K L D σ hgen SL hSL (μ₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (ν₀ e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (fun q hq => hur₀ e i₀ q hq) (hrel e he) pl pl' hpl hpl' hunder
      simp only [AP, BP, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
      refine Prod.ext ?_ ?_
      · show _ * (_ + _) = _ * (_ + _)
        rw [hq, hsum']
      · show _ * _ * _ = _ * _ * _
        rw [hq, mul_assoc, hprod', ← mul_assoc]
    · obtain ⟨M, hM, χ₁, χ₂, h1c, h1t, h2c, h2t, -, htabM⟩ :=
        AutomorphicForm.exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt L SL w hαm (μ₀ e) (ν₀ e)
          (hμ₀u e) (hν₀u e) (hμ₀ic e) (hν₀ic e) (hμ₀c e) (hν₀c e) (fun q hq => hur₀' e i₀ q hq)
      refine ⟨M, hM, χ₁, χ₂, h1c, h1t, h2c, h2t, fun pl hpl => ?_⟩
      rw [htn, hτ e 0 pl hpl, ← htabM pl hpl]
      simp only [AP, BP, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
      rfl

  · intro T hTd hT2 hTSL ws w' hw' ϖs hirr hϖs0 ns rTs hcos zs hzs
    have hsw : ∀ v ∈ T, (ws v).1.asIdeal = σ • (w' v).asIdeal := by
      intro v hv
      rw [hw' v hv, smul_smul, show σ * σ.symm = 1 from mul_eq_one_iff_eq_inv.mpr rfl, one_smul]
    have hunder' : ∀ v ∈ T, HeightOneSpectrum.under (𝓞 K) (w' v) = v := by
      intro v hv
      apply HeightOneSpectrum.ext
      have h2 : ((ws v).1.asIdeal).under (𝓞 K) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal (ws v).2
      show ((w' v).asIdeal).under (𝓞 K) = v.asIdeal
      rw [← h2, hsw v hv, under_smul_ideal]
    have hw'inj : Set.InjOn w' ↑T := fun v₁ h₁ v₂ h₂ heq => by
      rw [← hunder' v₁ h₁, ← hunder' v₂ h₂, heq]
    have hw'SL : ∀ v ∈ T, w' v ∉ SL := fun v hv => hTSL v hv (w' v) (hunder' v hv)
    have hwsSL : ∀ v ∈ T, (ws v).1 ∉ SL := fun v hv => hTSL v hv (ws v).1 (ws v).2
    set TL : Finset (HeightOneSpectrum (𝓞 L)) := T.image w' with hTL
    have hTLd : Disjoint TL SL := by
      rw [Finset.disjoint_left]
      intro pl hpl
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hpl
      exact hw'SL v hv
    have hTLc : 2 ≤ TL.card := by rw [Finset.card_image_of_injOn hw'inj]; exact hT2
    obtain ⟨Λ, hΛ, s, HPs⟩ := HP TL hTLd hTLc
    let incl : C(Xb, X) := ⟨Set.inclusion hXbX, continuous_inclusion hXbX⟩
    let res : C(X, ℂ) →L[ℂ] C(Xb, ℂ) :=
      { toFun := fun g => g.comp incl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := ContinuousMap.continuous_precomp incl }
    have hres : ∀ (g : C(X, ℂ)) (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (hy : y ∈ Xb),
        res g ⟨y, hy⟩ = g ⟨y, hXbX hy⟩ := fun _ _ _ => rfl
    refine ⟨Λ.comp res, s.comp res, ?_, ?_⟩
    ·
      intro τK ε hε
      let τL : HeightOneSpectrum (𝓞 L) → ℂ × ℂ := fun pl =>
        if h : ∃ v ∈ T, w' v = pl then τK (Classical.choose h) else 0
      have hτL : ∀ v ∈ T, τL (w' v) = τK v := by
        intro v hv
        have h : ∃ v' ∈ T, w' v' = w' v := ⟨v, hv, rfl⟩
        simp only [τL, dif_pos h]
        congr 1
        exact hw'inj (Classical.choose_spec h).1 hv (Classical.choose_spec h).2
      obtain ⟨UL, hUL, hΛε⟩ := hΛ τL ε hε
      refine ⟨fun v => UL (w' v), fun v hv => ⟨(hUL (w' v) (Finset.mem_image_of_mem w' hv)).1, ?_⟩,
        fun g hg0 hg1 => ?_⟩
      · rw [← hτL v hv]; exact (hUL (w' v) (Finset.mem_image_of_mem w' hv)).2
      · show ‖Λ (res g)‖ < ε
        refine hΛε (res g) (fun y hy => ?_) (fun y => ?_)
        · obtain ⟨pl, hpl, hy'⟩ := hy
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hpl
          rw [show res g y = g ⟨y, hXbX y.2⟩ from rfl]
          exact hg0 _ ⟨v, hv, hy'⟩
        · rw [show res g y = g ⟨y, hXbX y.2⟩ from rfl]; exact hg1 _
    · intro ks js φ hφ hφc φf hfact hbi harch g hg I R₂ hI
      let ksL : HeightOneSpectrum (𝓞 L) → ℕ := fun pl =>
        if h : ∃ v ∈ T, w' v = pl then ks (Classical.choose h) else 0
      let jsL : HeightOneSpectrum (𝓞 L) → ℕ := fun pl =>
        if h : ∃ v ∈ T, w' v = pl then js (Classical.choose h) else 0
      have hksL : ∀ v ∈ T, ksL (w' v) = ks v := by
        intro v hv
        have h : ∃ v' ∈ T, w' v' = w' v := ⟨v, hv, rfl⟩
        simp only [ksL, dif_pos h]
        congr 1
        exact hw'inj (Classical.choose_spec h).1 hv (Classical.choose_spec h).2
      have hjsL : ∀ v ∈ T, jsL (w' v) = js v := by
        intro v hv
        have h : ∃ v' ∈ T, w' v' = w' v := ⟨v, hv, rfl⟩
        simp only [jsL, dif_pos h]
        congr 1
        exact hw'inj (Classical.choose_spec h).1 hv (Classical.choose_spec h).2
      have hgb : ∀ x : Xb, res g x = ∏ pl ∈ TL,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) pl).1 ^ ksL pl *
            ((HeckeEigensystem.cNorm pl)⁻¹ * ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) pl).2) ^ jsL pl := by
        intro x
        rw [show res g x = g ⟨x, hXbX x.2⟩ from rfl, hg, Finset.prod_image hw'inj]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [hksL v hv, hjsL v hv]
      have hunrT : ∀ (e : ιE) (i : Fin (nE e)), ∀ v ∈ T,
          NumberField.TateGlobal.IsUnramifiedCharAt (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (ws v).1 ∧
          NumberField.TateGlobal.IsUnramifiedCharAt (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (ws v).1 := fun e i v hv =>
        ⟨htw_unr _ _ _ (hunrE e i _ (hwsSL v hv)).1, htw_unr _ _ _ (hunrE e i _ (hwsSL v hv)).2⟩
      have hae : {t : ℝ | t ≠ 0} ∈ MeasureTheory.ae (volume : Measure ℝ) := by
        rw [MeasureTheory.mem_ae_iff]
        have hc0 : {t : ℝ | t ≠ 0}ᶜ = {0} := by ext t; simp
        rw [hc0]; exact measure_singleton 0
      have key := HPs ksL jsL (res g) hgb I (max R₂ R₁) ?_
      · constructor
        ·
          haveI : CompactSpace Xb := isCompact_iff_compactSpace.mp hXbc
          refine Summable.of_norm_bounded (hsum.mul_right ‖res g‖) fun n => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← hres g (tabs n) (htabsb n)]
          exact (res g).norm_coe_le_norm ⟨tabs n, htabsb n⟩
        · have h2 := key.sub_const ((∑' n, cs n * res g ⟨tabs n, htabsb n⟩) + Λ (res g))
          rw [sub_self] at h2
          refine h2.congr' (Filter.Eventually.of_forall fun R => ?_)
          simp only [ContinuousLinearMap.comp_apply, hres]
          ring
      intro R hR
      have hR₂ : R₂ ≤ R := le_trans (le_max_left _ _) hR
      have hR₁ : R₁ ≤ R := le_trans (le_max_right _ _) hR
      rw [hI R hR₂]
      congr 1
      rw [tsum_eq_tsum_subtype_of_eq_zero Sset _ (fun e he => ?_)]
      · refine tsum_congr fun e => ?_
        have hunrTe : ∀ (i : Fin (nE e)), ∀ v ∈ T,
            NumberField.TateGlobal.IsUnramifiedCharAt (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (ws v).1 ∧
            NumberField.TateGlobal.IsUnramifiedCharAt (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (ws v).1 := fun i => hunrT e i
        rw [integral_comp_sub' _ (sh e)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with u hu
        simp only [aP, PP, QP, UP, VP]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        set t : ℝ := u - sh e with ht
        have hM := HMS (μE e) (νE e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
          (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i)
          (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j)
          (OE e i) (EE e i) (NE e i) (_hEE e i) (OE e j) (EE e j) (NE e j) (_hEE e j) t R hR₁
        have hcj : Continuous (φE e j ((t : ℂ) * Complex.I)) := (_hφEjc e j).comp (continuous_const.prodMk continuous_id)
        obtain ⟨hψ, hψc, hψsph⟩ :=
          AutomorphicForm.isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
            L SL N hN w hαm (μE e) (νE e) ((t : ℂ) * Complex.I) (φE e j ((t : ℂ) * Complex.I)) (_hφE e j _) hcj (_hφElev e j _)
        have h5 := AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isSemiLocalFactorization
          K L S T hTd SL hTSL ws ϖs hirr hϖs0 ns rTs hcos zs hzs φa φS ks js φ hφ hφc φf hfact φ₀ hφ₀c hφ₀s φf₀ (hφ₀T T hTd)
          hαm (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (hunrTe i) ((t : ℂ) * Complex.I) _ hψ hψc hψsph
        have hK : (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) =
                  (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            ((((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-((t : ℂ) * Complex.I)) +
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ ((t : ℂ) * Complex.I))) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              (((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) * a e i j t := by
          simp only [a]
          rw [← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          beta_reduce
          rw [h5]
          ring
        rw [hK]
        by_cases hAe : invA e
        · have hnc : ¬ isC e := fun h => h.1 hAe
          by_cases hd : dg e
          ·
            have hsh : sh e = θA e / 2 := by simp only [sh, if_pos hd]
            have h2tR : 2 * t + θA e = 2 * u := by rw [ht, hsh]; ring
            have h2t : 2 * (t : ℂ) + (θA e : ℂ) = 2 * (u : ℂ) := by exact_mod_cast h2tR
            have h2t0 : 2 * t + θA e ≠ 0 := by rw [h2tR]; exact mul_ne_zero two_ne_zero hu
            have hMd := hM.2.1 hAe.1 hAe.2 (θA e) (hθA e hd) h2t0
            rw [hMd]
            have hT : res g ⟨τP e u, hτX e u⟩ =
                      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            ((((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-((t : ℂ) * Complex.I)) +
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ ((t : ℂ) * Complex.I))) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              (((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) := by
              rw [hres, hg]
              refine Finset.prod_congr rfl fun v hv => ?_
              have hq : HeckeEigensystem.cNorm (ws v).1 = HeckeEigensystem.cNorm (w' v) :=
                AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul K L σ (w' v) (ws v).1 (hsw v hv)
              have hUμ := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).1
              have hUν := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).2
              simp only [τP, if_neg (hw'SL v hv)]
              rw [hq, ← hUμ, ← hUν, ht, hsh]
              obtain ⟨h1, h2⟩ := hinv_fwd e hAe (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)))
              simp only [μ₀, ν₀, if_pos hd, MonoidHom.mul_apply, Units.val_mul, hcpσ, h1, h2,
                hcpdet, neg_neg, cNorm_cpow_neg_sub, cNorm_cpow_sub]
              have hCC := cNorm_cpow_mul_neg (w' v) ((((θA e / 2 : ℝ)) : ℂ) * Complex.I)
              congr 1
              · congr 1
                ring
              · congr 1
                linear_combination (HeckeEigensystem.cNorm (w' v))⁻¹ * HeckeEigensystem.cNorm (w' v) *
                  ((μE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                  ((νE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                  ((HeckeEigensystem.cNorm (w' v)) ^ (-(((w / 2 : ℝ) : ℂ)))) ^ 2 * hCC
            have hdc : dg e ∨ isC e := Or.inl hd
            have hexp1 : Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θA e : ℂ)) = 2 * Complex.I * (R : ℂ) * (u : ℂ) := by
              rw [h2t]; ring
            have hexp2 : Complex.I * (2 * (t : ℂ) + (θA e : ℂ)) = 2 * Complex.I * (u : ℂ) := by
              rw [h2t]; ring

            rw [if_pos hAe, if_pos hAe, if_pos hdc, if_pos hdc, hexp1, hexp2, hT]
          ·
            have hsh : sh e = 0 := by simp only [sh, if_neg hd, if_neg hnc]
            have hoff : ∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z ≠ νE e z := by
              by_contra hcon; push Not at hcon; exact hd ⟨hAe, hcon⟩
            have ht0 : t ≠ 0 := by rw [ht, hsh, sub_zero]; exact hu
            have hMo := hM.2.2.1 hAe.1 hAe.2 hoff ht0
            rw [hMo]
            have hndc : ¬ (dg e ∨ isC e) := fun h => h.elim hd hnc
            have hT : res g ⟨τP e u, hτX e u⟩ =
                      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            ((((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-((t : ℂ) * Complex.I)) +
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ ((t : ℂ) * Complex.I))) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              (((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) := by
              rw [hres, hg]
              refine Finset.prod_congr rfl fun v hv => ?_
              have hq : HeckeEigensystem.cNorm (ws v).1 = HeckeEigensystem.cNorm (w' v) :=
                AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul K L σ (w' v) (ws v).1 (hsw v hv)
              have hUμ := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).1
              have hUν := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).2
              simp only [τP, if_neg (hw'SL v hv)]
              rw [hq, ← hUμ, ← hUν, ht, hsh]
              obtain ⟨h1, h2⟩ := hinv_fwd e hAe (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)))
              simp only [μ₀, ν₀, if_neg hd, if_neg hnc, MonoidHom.mul_apply, Units.val_mul, hcpσ, h1, h2, sub_zero]
            rw [if_pos hAe, if_pos hAe, if_neg hndc, if_neg hndc]
            rw [hT, ht, hsh, sub_zero]
            ring
        ·
          have hc : isC e := e.2.resolve_left hAe
          have hnd : ¬ dg e := fun h => hAe h.1
          have hsh : sh e = τC e / 2 := by simp only [sh, if_neg hnd, if_pos hc]
          have h2tR : 2 * t + τC e = 2 * u := by rw [ht, hsh]; ring
          have h2t : 2 * (t : ℂ) + (τC e : ℂ) = 2 * (u : ℂ) := by exact_mod_cast h2tR
          have h2t0 : 2 * t + τC e ≠ 0 := by rw [h2tR]; exact mul_ne_zero two_ne_zero hu
          have hninv : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
              μE e (D.unitsAct σ.symm z) ≠ μE e z ∨ νE e (D.unitsAct σ.symm z) ≠ νE e z := by
            by_contra hcon; push Not at hcon; exact hAe ⟨fun z => (hcon z).1, fun z => (hcon z).2⟩
          have hMc := hM.2.2.2.2 (τC e) (hτC e hc).1 (hτC e hc).2 hninv h2t0
          rw [hMc]
          have hT : res g ⟨τP e u, hτX e u⟩ =
                    (∏ v ∈ T,
        ((HeckeEigensystem.cNorm (ws v).1) ^ ((1 / 2 : ℝ) : ℂ) *
            ((((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ (-((t : ℂ) * Complex.I)) +
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
                (HeckeEigensystem.cNorm (ws v).1) ^ ((t : ℂ) * Complex.I))) ^ ks v *
          ((HeckeEigensystem.cNorm (ws v).1)⁻¹ *
            ((HeckeEigensystem.cNorm (ws v).1) *
              (((μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ) *
              (((νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (ws v).1)) : ℂˣ) : ℂ))) ^ js v) := by
              rw [hres, hg]
              refine Finset.prod_congr rfl fun v hv => ?_
              have hq : HeckeEigensystem.cNorm (ws v).1 = HeckeEigensystem.cNorm (w' v) :=
                AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul K L σ (w' v) (ws v).1 (hsw v hv)
              have hUμ := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (μE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).1
              have hUν := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_det_heckeGen_eq_apply_det_heckeGen_of_asIdeal_eq_smul_of_isUnramifiedCharAt K L D σ (νE e * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (w' v) (ws v).1 (hsw v hv) (hunrTe i v hv).2
              simp only [τP, if_neg (hw'SL v hv)]
              rw [hq, ← hUμ, ← hUν, ht, hsh]
              obtain ⟨e1, e2⟩ := hC_fwd e hc (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)))
              simp only [μ₀, ν₀, if_neg hnd, if_pos hc, MonoidHom.mul_apply, Units.val_mul, hcpσ, e1, e2,
                hcpdet, neg_neg, cNorm_cpow_neg_sub, cNorm_cpow_sub]
              have hCC := cNorm_cpow_mul_neg (w' v) ((((τC e / 2 : ℝ)) : ℂ) * Complex.I)
              have hEE := cNorm_cpow_mul_neg (w' v) ((τC e : ℂ) * Complex.I)
              have hEC : HeckeEigensystem.cNorm (w' v) ^ (-((τC e : ℂ) * Complex.I)) *
                  HeckeEigensystem.cNorm (w' v) ^ ((((τC e / 2 : ℝ)) : ℂ) * Complex.I) =
                  HeckeEigensystem.cNorm (w' v) ^ (-((((τC e / 2 : ℝ)) : ℂ) * Complex.I)) := by
                rw [← cNorm_cpow_add]; congr 1; push_cast; ring
              have hE'C' : HeckeEigensystem.cNorm (w' v) ^ ((τC e : ℂ) * Complex.I) *
                  HeckeEigensystem.cNorm (w' v) ^ (-((((τC e / 2 : ℝ)) : ℂ) * Complex.I)) =
                  HeckeEigensystem.cNorm (w' v) ^ ((((τC e / 2 : ℝ)) : ℂ) * Complex.I) := by
                rw [← cNorm_cpow_add]; congr 1; push_cast; ring
              congr 1
              · congr 1
                linear_combination
                  (HeckeEigensystem.cNorm (w' v)) ^ ((1 / 2 : ℝ) : ℂ) *
                    ((νE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                    (HeckeEigensystem.cNorm (w' v)) ^ (-(((w / 2 : ℝ) : ℂ))) *
                    HeckeEigensystem.cNorm (w' v) ^ (-((u : ℂ) * Complex.I)) * (-hEC) +
                  (HeckeEigensystem.cNorm (w' v)) ^ ((1 / 2 : ℝ) : ℂ) *
                    ((μE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                    (HeckeEigensystem.cNorm (w' v)) ^ (-(((w / 2 : ℝ) : ℂ))) *
                    HeckeEigensystem.cNorm (w' v) ^ ((u : ℂ) * Complex.I) * (-hE'C')
              · congr 1
                linear_combination (HeckeEigensystem.cNorm (w' v))⁻¹ * HeckeEigensystem.cNorm (w' v) *
                  ((μE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                  ((νE e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) : ℂˣ) : ℂ) *
                  ((HeckeEigensystem.cNorm (w' v)) ^ (-(((w / 2 : ℝ) : ℂ)))) ^ 2 * (hCC - hEE)
          have hdc : dg e ∨ isC e := Or.inr hc
          rw [if_neg hAe, if_neg hAe, if_pos hdc, if_pos hdc]
          rw [show Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τC e : ℂ)) = 2 * Complex.I * (R : ℂ) * (u : ℂ) by rw [h2t]; ring,
            show Complex.I * (2 * (t : ℂ) + (τC e : ℂ)) = 2 * Complex.I * (u : ℂ) by rw [h2t]; ring, hT]
          ring
      ·
        have hnA : ¬ invA e := fun h => he (Or.inl h)
        have hnC : ∀ τ, ¬ Csh e τ := fun τ h => he (Or.inr ⟨hnA, τ, h⟩)
        have hninv : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
            μE e (D.unitsAct σ.symm z) ≠ μE e z ∨ νE e (D.unitsAct σ.symm z) ≠ νE e z := by
          by_contra hcon; push Not at hcon; exact hnA ⟨fun z => (hcon z).1, fun z => (hcon z).2⟩
        have hG : ∀ (t : ℝ) (i j : Fin (nE e)), _ := fun t i j =>
          ((HMS (μE e) (νE e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
            (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i)
            (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j)
            (OE e i) (EE e i) (NE e i) (_hEE e i) (OE e j) (EE e j) (NE e j) (_hEE e j) t R hR₁).2.2.2.1
            hninv (fun τ => hnC τ))
        simp only [hG, mul_zero, Finset.sum_const_zero, integral_zero]

end S_AutomorphicForm_exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization (solution)
