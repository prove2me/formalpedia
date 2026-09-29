-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c6014250-c6ae-5e4a-b945-6e7572a11b8e

import Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub
import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

namespace R3TwSCut

open AutomorphicForm

section Transport

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem sigmaAdelicAct_symm_apply (σ : L ≃ₐ[K] L) (x : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L D σ.symm (sigmaAdelicAct K L D σ x) = x := by
  have h : sigmaAdelicAct K L D (σ.symm * σ) = MonoidHom.id _ := by
    rw [show σ.symm * σ = 1 from ?_, sigmaAdelicAct_one]
    ext y
    exact σ.symm_apply_apply y
  have := congrArg (fun f => f x) (sigmaAdelicAct_mul K L D σ.symm σ)
  simpa [h] using this.symm

theorem sigmaAdelicAct_apply_symm (σ : L ≃ₐ[K] L) (x : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L D σ (sigmaAdelicAct K L D σ.symm x) = x := by
  simpa using sigmaAdelicAct_symm_apply K L D σ.symm x

theorem sigmaAdelicAct_globalPoints' (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) :=
  sigmaAdelicAct_globalPoints K L D σ γ

omit [NumberField L] in
theorem map_symm_map (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)
        (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) = γ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show σ.symm (σ (γ i j)) = γ i j
  exact σ.symm_apply_apply _

omit [NumberField L] in
theorem map_map_symm (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L)
        (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) γ) = γ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show σ (σ.symm (γ i j)) = γ i j
  exact σ.apply_symm_apply _

omit [NumberField L] in
theorem bijective_map (σ : L ≃ₐ[K] L) :
    Function.Bijective (Matrix.GeneralLinearGroup.map (n := Fin 2) (σ : L →+* L)) :=
  ⟨fun a b h => by
      simpa [map_symm_map K L σ] using
        congrArg (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) h,
    fun c => ⟨Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) c, map_map_symm K L σ c⟩⟩

theorem twistedAdelicKernel_eq_adelicKernel_comp (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) :
    (fun y => twistedAdelicKernel L (sigmaAdelicAct K L D σ.symm) φ x y) =
      fun y => adelicKernel L (φ ∘ sigmaAdelicAct K L D σ.symm) (sigmaAdelicAct K L D σ x) y := by
  funext y
  unfold twistedAdelicKernel adelicKernel
  refine (finsum_eq_of_bijective (Matrix.GeneralLinearGroup.map (n := Fin 2) (σ : L →+* L))
    (bijective_map K L σ) fun γ => ?_)
  simp only [Function.comp_apply, map_mul, map_inv, sigmaAdelicAct_symm_apply,
    sigmaAdelicAct_globalPoints', map_symm_map]

theorem comp_fold_integrand (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) (γ : GL (Fin 2) L)
    (w y : AdelicGL2 (𝓞 L) L) :
    (φ ∘ sigmaAdelicAct K L D σ.symm) ((sigmaAdelicAct K L D σ x)⁻¹ * globalPoints (𝓞 L) L γ * (w * y)) =
      φ (x⁻¹ * globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) γ) *
        sigmaAdelicAct K L D σ.symm (w * y)) := by
  simp only [Function.comp_apply, map_mul, map_inv, sigmaAdelicAct_symm_apply,
    sigmaAdelicAct_globalPoints']

noncomputable def sigmaHomeomorph (σ : L ≃ₐ[K] L) : AdelicGL2 (𝓞 L) L ≃ₜ AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L D σ
  invFun := sigmaAdelicAct K L D σ.symm
  left_inv := sigmaAdelicAct_symm_apply K L D σ
  right_inv := sigmaAdelicAct_apply_symm K L D σ
  continuous_toFun := continuous_sigmaAdelicAct K L D σ
  continuous_invFun := continuous_sigmaAdelicAct K L D σ.symm

theorem hasCompactSupport_comp_sigmaAdelicAct (σ : L ≃ₐ[K] L) {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (φ ∘ sigmaAdelicAct K L D σ.symm) :=
  hφc.comp_homeomorph (sigmaHomeomorph K L D σ.symm)

end Transport

section Height

variable (F : Type) [Field F] [NumberField F]

open NumberField.AdelicHeight AutomorphicForm.WindowedSiegel

theorem finLocalHeight_scalar_mul {k : Type*} [NormedField k] {a : k} (ha : a ≠ 0)
    (s g : GL (Fin 2) k)
    (h00 : (s : Matrix (Fin 2) (Fin 2) k) 0 0 = a) (h01 : (s : Matrix (Fin 2) (Fin 2) k) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) k) 1 1 = a) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (s : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) := rfl
  have hs : (s : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have hmul : ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (g : Matrix (Fin 2) (Fin 2) k) := by
    rw [hcoe, hs, smul_mul_assoc, one_mul]
  have hdet : ‖((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det‖ =
      ‖a‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) k).det‖ := by
    rw [hmul, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow]
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ‖a‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := by
    unfold rowMaxNorm
    rw [hmul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, norm_mul, norm_mul,
      mul_max_of_nonneg _ _ (norm_nonneg a)]
  have ha' : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow]
  field_simp

theorem idele_arch_ne_zero (z : (AdeleRing (𝓞 F) F)ˣ) (v : InfinitePlace F) :
    (z : AdeleRing (𝓞 F) F).1 v ≠ 0 :=
  (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero

theorem idele_fin_ne_zero (z : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (z : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
  (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1)
      (idele_arch_ne_zero F z) ?_ ?_ ?_ ?_ _
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_mul (a := (z : AdeleRing (𝓞 F) F).2 v) (idele_fin_ne_zero F z v)
      _ _ ?_ ?_ ?_ ?_
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl

end Height

section Pins

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem isFiniteMeasure_productionPinsOf_ν (Dm : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    @IsFiniteMeasure _ (productionPinsOf F Dm U gen (adelicBox F)).nS
      (productionPinsOf F Dm U gen (adelicBox F)).ν := by
  show IsFiniteMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
  infer_instance

theorem measurable_unipotentGL2 :
    Measurable fun t : AdeleRing (𝓞 F) F => (unipotentGL2 t : AdelicGL2 (𝓞 F) F) :=
  (continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).measurable

theorem exists_isCompact_ae_unipotentGL2_mem (Dm : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    ∃ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C ∧
      ∀ᵐ q ∂(productionPinsOf F Dm U gen (adelicBox F)).ν, (unipotentGL2 q : AdelicGL2 (𝓞 F) F) ∈ C := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  refine ⟨(fun t : AdeleRing (𝓞 F) F => (unipotentGL2 t : AdelicGL2 (𝓞 F) F)) '' C,
    hC.image continuous_unipotentGL2, ?_⟩
  show ∀ᵐ q ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), _
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 F) F) (measurableSet_adelicBox F)]
    with q hq
  exact ⟨q, hsub hq, rfl⟩

end Pins

section Reindex

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

omit [NumberField L] in

theorem center_le_comap_map (τ : L ≃+* L) :
    Subgroup.center (GL (Fin 2) L) ≤
      (Subgroup.center (GL (Fin 2) L)).comap
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (τ : L →+* L)) := by
  intro s hs
  rw [Subgroup.mem_comap]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs ⊢
  obtain ⟨a, rfl⟩ := hs
  exact ⟨Units.map ((τ : L →+* L) : L →* L) a, (map_scalar (τ : L →+* L) a).symm⟩

noncomputable def quotMap (τ : L ≃+* L) :
    GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L) →* GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L) :=
  QuotientGroup.map _ _ (Matrix.GeneralLinearGroup.map (n := Fin 2) (τ : L →+* L))
    (center_le_comap_map L τ)

omit [NumberField L] in
theorem quotMap_mk (τ : L ≃+* L) (g : GL (Fin 2) L) :
    quotMap L τ (g : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)) =
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (τ : L →+* L) g :
        GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)) :=
  QuotientGroup.map_mk _ _ _ _ g

omit [NumberField L] in
theorem bijective_quotMap (σ : L ≃ₐ[K] L) :
    Function.Bijective (quotMap L (σ.symm : L ≃+* L)) := by
  have h1 : ∀ q, quotMap L (σ : L ≃+* L) (quotMap L (σ.symm : L ≃+* L) q) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [quotMap_mk, quotMap_mk]
      exact congrArg _ (map_map_symm K L σ g)
  have h2 : ∀ q, quotMap L (σ.symm : L ≃+* L) (quotMap L (σ : L ≃+* L) q) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [quotMap_mk, quotMap_mk]
      exact congrArg _ (map_symm_map K L σ g)
  exact Function.bijective_iff_has_inverse.mpr ⟨quotMap L (σ : L ≃+* L), h1, h2⟩

omit [NumberField L] in

theorem exists_out_eq_mul_scalar (g : GL (Fin 2) L) :
    ∃ a : Lˣ, (g : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)).out =
      g * Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) L)) g
  have hc : (h : GL (Fin 2) L) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2) : Lˣ →* GL (Fin 2) L).range := by
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact h.2
  obtain ⟨a, ha⟩ := hc
  exact ⟨a, by rw [hh, ← ha]⟩

theorem globalPoints_scalar (a : Lˣ) :
    globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a) :=
  map_scalar (algebraMap L (AdeleRing (𝓞 L) L)) a

theorem sigmaAdelicAct_centralScalar (τ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D τ (centralScalar (𝓞 L) L w) =
      centralScalar (𝓞 L) L
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) w) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom w

theorem unitsMap_act_symm_principal (σ : L ≃ₐ[K] L) (a : Lˣ) :
    Units.map ((D.act σ.symm : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
          (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a)) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a := by
  refine Units.ext ?_
  show (D.act σ.symm) (algebraMap L (AdeleRing (𝓞 L) L) (σ (a : L))) = algebraMap L (AdeleRing (𝓞 L) L) a
  rw [D.compat]
  exact congrArg _ (σ.symm_apply_apply (a : L))

theorem globalPoints_mul_scalar_mul_sigmaAdelicAct (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) (a : Lˣ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
        sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y) =
      globalPoints (𝓞 L) L g *
        sigmaAdelicAct K L D σ.symm
          (centralScalar (𝓞 L) L
              (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
                  (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) * z) * y) := by
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, globalPoints_scalar,
    sigmaAdelicAct_centralScalar K L D σ.symm
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
        (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a)),
    unitsMap_act_symm_principal K L D σ a]
  simp only [mul_assoc]

theorem integral_fold_mul_scalar
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L) (g : GL (Fin 2) L) (a : Lˣ) :
    ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (x⁻¹ * globalPoints (𝓞 L) L (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y)) ∂νZL =
      ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (x⁻¹ * globalPoints (𝓞 L) L g *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y)) ∂νZL := by
  have hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξL ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
            (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) * z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
    intro z
    have hmul : (⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
          (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) * z, Subgroup.mem_top _⟩ :
          (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
        ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
            (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a), Subgroup.mem_top _⟩ *
          ⟨z, Subgroup.mem_top z⟩ := rfl
    rw [hmul, map_mul, hξt _ ⟨Units.map ((σ : L ≃ₐ[K] L) : L →* L) a, rfl⟩, one_mul]
  have hpt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a) *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y)) =
        (fun w : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L g *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L w * y)))
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
            (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) * z) := by
    intro z
    beta_reduce
    rw [hξ z, mul_assoc x⁻¹, globalPoints_mul_scalar_mul_sigmaAdelicAct K L D σ g a z y,
      ← mul_assoc x⁻¹]
  calc
    _ = ∫ z, (fun w : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L g *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L w * y)))
          (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
            (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a) * z) ∂νZL :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = _ :=
      MeasureTheory.integral_mul_left_eq_self (μ := νZL)
        (fun w : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L g *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L w * y)))
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
          (Units.map ((σ : L ≃ₐ[K] L) : L →* L) a))

theorem finsum_foldIntegral_map_symm_eq
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) :
    (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) q.out) *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y)) ∂νZL) =
      fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * globalPoints (𝓞 L) L q.out *
            sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * y)) ∂νZL := by
  funext y
  refine finsum_eq_of_bijective (quotMap L (σ.symm : L ≃+* L)) (bijective_quotMap K L σ)
    fun q => ?_
  have hq : quotMap L (σ.symm : L ≃+* L) q =
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (σ.symm : L →+* L) q.out :
        GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)) := by
    have := quotMap_mk L (σ.symm : L ≃+* L) q.out
    rwa [QuotientGroup.out_eq'] at this
  obtain ⟨a, ha⟩ := exists_out_eq_mul_scalar L
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (σ.symm : L →+* L) q.out)
  rw [hq, ha]
  exact (integral_fold_mul_scalar K L D νZL σ ξL hξt φ x y _ a).symm

end Reindex

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem setIntegral_mul_lambdaT_twistedAdelicKernel_eq
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (ΦL : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (T : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (@AutomorphicForm.lambdaT _ (productionPinsOf L ΦL U gen (adelicBox L)).nS _ _
          (productionPinsOf L ΦL U gen (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T
          (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y)
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL =
      @AutomorphicForm.lambdaT _ (productionPinsOf L ΦL U gen (adelicBox L)).nS _ _
        (productionPinsOf L ΦL U gen (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) T
        (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * globalPoints (𝓞 L) L q.out *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
        x := by
  haveI := isFiniteMeasure_productionPinsOf_ν L ΦL U gen
  rw [twistedAdelicKernel_eq_adelicKernel_comp K L D σ φ x]
  obtain ⟨-, h⟩ :=
    AutomorphicForm.integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
      L νZL ΩL hΩL ξL hξc hξt (φ ∘ sigmaAdelicAct K L D σ.symm)
      (hφ.comp (continuous_sigmaAdelicAct K L D σ.symm)) (hasCompactSupport_comp_sigmaAdelicAct K L D σ hφc)
      (productionPinsOf L ΦL U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
      (measurable_unipotentGL2 L) (exists_isCompact_ae_unipotentGL2_mem L ΦL U gen)
      (NumberField.AdelicHeight.adelicHeight L) (adelicHeight_centralScalar_mul L) T
      (sigmaAdelicAct K L D σ x) x
  rw [h]
  simp_rw [comp_fold_integrand]
  rw [finsum_foldIntegral_map_symm_eq K L D νZL σ ξL hξt φ x]

end Fold

end R3TwSCut

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
open AutomorphicForm in
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
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
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
    Filter.Tendsto (fun R : ℝ =>
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y)
            (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  twistedCutTrace K L D σ
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0)
    := by

  obtain ⟨tabs, htabs, cs, hsum, hatoms, hrest⟩ :=
    AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt N hN tysL S φa φS X hX c u d₁ d₂ hc
      Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
  refine ⟨tabs, htabs, cs, hsum, hatoms, ?_⟩
  intro T hTS hT2 hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hcos zs hzs
  obtain ⟨μ, ν, hnoatom, hR⟩ := hrest T hTS hT2 hTSL ws w' hw' ϖs hϖ hϖs0 ns rTs hcos zs hzs
  refine ⟨μ, ν, hnoatom, ?_⟩
  intro ks js φ hφ hφc φf hfac hbi hfin g hg

  refine (hR ks js φ hφ hφc φf hfac hbi hfin g hg).congr fun R => ?_
  congr 1
  congr 1
  funext x
  exact (R3TwSCut.setIntegral_mul_lambdaT_twistedAdelicKernel_eq K L D νZL ΩL hΩL σ ξL hξc hξt ΦL
    (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w)
    φ hφ hφc (Real.exp R) x).symm

end S_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub (solution)
