-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9a39edd5-a77f-558f-91ea-1d738a30f523

import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one
import Theorems.Thm_AutomorphicForm_lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
import Theorems.Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R4TwistSigmaDecomp

open NumberField.TateGlobal

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

noncomputable def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
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
    convert Set.image_id s <;> first | (funext a; exact θ.apply_symm_apply a) | exact θ.apply_symm_apply _
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

theorem continuous_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct σ z := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)
    exact (D.continuous_act σ).comp Units.continuous_val
  · show Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    exact (D.continuous_act σ).comp Units.continuous_coe_inv

theorem unitsAct_map_algebraMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) a) :=
  Units.ext (D.compat σ a)

end Modulus

section NormPow

variable (L : Type) [Field L] [NumberField L]

noncomputable def normPowC (s : ℝ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun z := Units.mk0 (((ideleNorm L z) ^ s : ℝ) : ℂ)
    (by exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos z) s).ne')
  map_one' := by
    ext
    simp only [Units.val_mk0, Units.val_one]
    have h1 : ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
      have := ideleNorm_mul (1 : (AdeleRing (𝓞 L) L)ˣ) 1
      rw [one_mul] at this
      have hp := ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)
      nlinarith [this, hp]
    rw [h1, Real.one_rpow]; norm_num
  map_mul' x y := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [ideleNorm_mul, Real.mul_rpow (ideleNorm_pos x).le (ideleNorm_pos y).le]
    push_cast; ring

theorem normPowC_apply (s : ℝ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((normPowC L s z : ℂˣ) : ℂ) = (((ideleNorm L z) ^ s : ℝ) : ℂ) := rfl

theorem ideleNorm_map_algebraMap (a : Lˣ) :
    ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a) = 1 := by
  have hA : Matrix.det (Matrix.diagonal ![(a : L), 1]) ≠ 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA) = a := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := L) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA)
  rw [AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_det, hdet] at h
  exact h

private theorem _root_.R4TwistSigmaDecomp.exists_notMem_finset (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 L), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 L)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 L)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "R4TwistSigmaDecomp" "exists_notMem_finset"
end NormPow

end R4TwistSigmaDecomp

open AutomorphicForm R4TwistSigmaDecomp in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
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
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
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
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ κ : ℝ, 0 < κ ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
        b i ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
      (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
      (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
      (hbs : ∀ π ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
      (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
        IsSmoothCuspAutomorphicFnAt L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
        Continuous ψ →
        (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
        ψ ∈ archCutSubmodule L tysL →
        (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
        ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0)
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
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ),
      IsFactorizableTestFn L φ →
      IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
      IsArchBiFinite L tysL φ →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
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
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
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
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L))‖) ∧
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
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
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  intro αm hαm
  classical

  have hξ't : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ' ⟨z, Subgroup.mem_top z⟩ = 1 := by
    rintro z ⟨a, rfl⟩
    rw [hξ', unitsAct_map_algebraMap]
    exact hξt _ ⟨Units.map (σ : L →* L) a, rfl⟩
  have hξ'c : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    have heq : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) =
        (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∘
          (fun z : (AdeleRing (𝓞 L) L)ˣ => D.unitsAct σ z) := by
      funext z; simp only [Function.comp_apply, hξ']
    rw [heq]
    exact hξc.comp (continuous_unitsAct K L D σ)
  have hξ'w : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) := by
    intro z; rw [hξ', hξw, ideleNorm_unitsAct]

  let ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ :=
    ξ' * (normPowC L (-w)).comp (Subgroup.subtype (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ))
  have hξ₀v : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
      ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (-w) : ℝ) : ℂ) := by
    intro z
    show (((ξ' * (normPowC L (-w)).comp (Subgroup.subtype (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)))
      ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, normPowC_apply]
    rfl
  have hnw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      (((NumberField.TateGlobal.ideleNorm L z) ^ (-w) : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = 1 := by
    intro z
    have hp := NumberField.TateGlobal.ideleNorm_pos z
    rw [← Complex.ofReal_mul, Real.rpow_neg hp.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hp w).ne']
    simp
  have hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro z; rw [hξ₀v, mul_assoc, hnw, mul_one]
  have hξ₀c : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    have heq : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) =
        fun z => ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm L z) ^ (-w) : ℝ) : ℂ) := funext hξ₀v
    rw [heq]
    refine hξ'c.mul (Complex.continuous_ofReal.comp ?_)
    exact (NumberField.TateGlobal.continuous_ideleNorm L).rpow_const
      (fun z => Or.inl (NumberField.TateGlobal.ideleNorm_pos z).ne')
  have hξ₀t : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ₀ ⟨z, Subgroup.mem_top z⟩ = 1 := by
    intro z hz
    apply Units.ext
    rw [hξ₀v z, hξ't z hz]
    obtain ⟨a, rfl⟩ := hz
    rw [ideleNorm_map_algebraMap, Real.one_rpow]
    simp
  have hξ₀u : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ‖((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    have hp := NumberField.TateGlobal.ideleNorm_pos z
    rw [hξ₀v, norm_mul, hξ'w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _), Real.rpow_neg hp.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hp w).ne']

  obtain ⟨-, -, -, hΦcs, hΦc⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum L α β hα hαβ
  have hN0 : N ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv⟩ := exists_notMem_finset L SL
    exact hv (hN v (by rw [hbot]; exact dvd_zero _))
  obtain ⟨ι', b', cls', hb', hb'n, hb'o, hb's, hb'c⟩ :=
    AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
      L α β hα hαβ (AutomorphicForm.canonicalTruncationDomain L α β) hΦcs hΦc ξ₀ N hN0 SL hN tysL

  obtain ⟨κ, hκ, HX⟩ :=
    AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ SL ξ₀ hξ₀c hξ₀t N hN tysL c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ hξ₀u hαm
  refine ⟨κ, hκ, ?_⟩
  intro ι b cls hb hb₁ hb₀ hbs hbc ιE _iC μE νE _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK
    _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE φ hφ hφc hfact hbi harch

  have hbi₀ : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ :=
    AutomorphicForm.IsBiInvariantUnder.mono L
      (inf_le_inf_right (finiteAdelicGL2Subgroup L) (principalLevel_le_levelOne (𝓞 L) L N)) hbi
  obtain ⟨hφ'cont, hφ'cs, hφ'fact, hφ'bi, hφ'arch⟩ :=
    AutomorphicForm.isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow L N tysL w φ hφ hφc hfact hbi₀ harch
  set φ' : AdelicGL2 (𝓞 L) L → ℂ := fun g : AdelicGL2 (𝓞 L) L => φ g *
        (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) with hφ'def
  have hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) := fun g => rfl

  have _hμν₀ : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ), μE e z * νE e z = ξ₀ ⟨z, Subgroup.mem_top z⟩ := by
    intro e z
    apply Units.ext
    rw [Units.val_mul, hξ₀v, ← _hμν e z, mul_assoc, mul_comm ((((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ)),
      hnw, mul_one]
  have _hpairs₀ : ∀ (μE' νE' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μE' → IsUnitaryChar (𝓞 L) L νE' →
        IsIdeleClassChar (𝓞 L) L μE' → IsIdeleClassChar (𝓞 L) L νE' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, μE' z * νE' z = ξ₀ ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μE' αm hαm ((t : ℂ) * Complex.I)) (etaSnd νE' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = μE' z ∧ νE e z = νE' z := by
    intro μE' νE' h1 h2 h3 h4 h5 h6 hprod
    refine _hpairs μE' νE' h1 h2 h3 h4 h5 h6 ?_
    intro z
    have hz := congrArg (fun u : ℂˣ => (u : ℂ)) (hprod z)
    simp only [Units.val_mul] at hz
    rw [hz, hξ₀]

  obtain ⟨R₀, HR⟩ := HX ι' b' cls' hb' hb'n hb'o hb's hb'c ιE μE νE _hμ _hν _hμic _hνic _hμc _hνc _hμν₀ _hdist nE φE
    _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs₀ OE EE NE _hEE
    φ' hφ'cont hφ'cs hφ'fact hφ'bi hφ'arch
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hXint, hXe, hXsum, hXeq⟩ := HR R hR
  have HT :=
    AutomorphicForm.lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
      K L α β hα hαβ ΦL νZL ΩL D σ ξL hξt Φ₀ hΦ₀s hΦ₀ w hξw ξ' hξ' ξ₀ hξ₀ φ φ' hφ' R
  obtain ⟨hCS1, hCS2, hCS3⟩ :=
    AutomorphicForm.integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ SL ξL hSL hξc hξt N hN tysL c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ w hξw ξ' hξ'
      ξ₀ hξ₀ ι b cls hb hb₁ hb₀ hbs hbc ι' b' cls' hb' hb'n hb'o hb's hb'c φ φ' hφ' hφ hφc hfact hbi harch R

  have hcoef : ∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ),
      (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) =
      (∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) φ' (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) := by
    intro e i j t
    congr 1
    funext k
    rw [(HT 1).2.2 (φE e j ((t : ℂ) * Complex.I)) k]

  have key : ∀ x : AdelicGL2 (𝓞 L) L,
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)) =
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ' (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξ₀ χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, φ' g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) +
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)) := by
    intro x
    rw [(HT x).1, (HT x).2.1]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hs : IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ' (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξ₀ χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, φ' g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) +
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x))) Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := hXint.add (hCS2.sub hCS1)
    exact hs.congr (ae_of_all _ fun x => (key x).symm)
  ·
    intro e
    simp only [hcoef]
    exact hXe e
  ·
    simp only [hcoef]
    exact hXsum
  ·
    simp only [hcoef]
    have hint : (∫ x in Φ₀,
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in Φ₀, (((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ' (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξ₀ χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, φ' g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) +
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x))) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
      integral_congr_ae (ae_of_all _ fun x => key x)
    have hg : IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)) Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := hCS2.sub hCS1
    rw [hint, integral_add hXint hg, integral_sub hCS2 hCS1, hCS3, sub_self, add_zero]
    exact hXeq

end S_AutomorphicForm_exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct (solution)
