-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/23f48035-d212-55d3-a218-cece7323928d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
import Theorems.Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.gl2Weyl_val EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped NNReal

namespace S24HeightFurniture

variable (K : Type) [Field K] [NumberField K]

theorem rowMaxNorm_scalar_shape_mul {K₀ : Type*} [NormedField K₀] {s : GL (Fin 2) K₀} {z : K₀}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    NumberField.AdelicHeight.rowMaxNorm ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = ‖z‖ * NumberField.AdelicHeight.rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K₀) := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have e10 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 0
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have e11 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 1
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold NumberField.AdelicHeight.rowMaxNorm
  rw [hcoe, e10, e11, norm_mul, norm_mul, mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_shape_mul {K₀ : Type*} [NormedField K₀] {s : GL (Fin 2) K₀} {z : K₀}
    (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    NumberField.AdelicHeight.finLocalHeight (s * g) = NumberField.AdelicHeight.finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K₀).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hz2 : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  unfold NumberField.AdelicHeight.finLocalHeight
  rw [rowMaxNorm_scalar_shape_mul h10 h11 g, hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ hz2]

theorem adelicHeight_scalar_shape_mul {s : AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers K) K} {ζ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) 0 0 = ζ)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) 1 1 = ζ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    NumberField.AdelicHeight.adelicHeight K (s * g) = NumberField.AdelicHeight.adelicHeight K g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)).det = ζ * ζ := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero]
  have hζ : IsUnit ζ := by
    have hu := Matrix.isUnits_det_units s
    rw [hdets] at hu
    exact (IsUnit.mul_iff.mp hu).1
  unfold NumberField.AdelicHeight.adelicHeight
  rw [map_mul, map_mul]
  have harch : AutomorphicForm.WindowedSiegel.archHeight K (NumberField.AdelicLevel.glArch
        (NumberField.RingOfIntegers K) K s *
        NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers K) K g) =
        AutomorphicForm.WindowedSiegel.archHeight K (NumberField.AdelicLevel.glArch
        (NumberField.RingOfIntegers K) K g) := by
    refine AutomorphicForm.WindowedSiegel.archHeight_scalar_entries_mul K (z := ζ.1) ?_ ?_ ?_ ?_ ?_
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers K) K g)
    · intro w
      exact ((hζ.map (NumberField.AdelicLevel.adeleArch (NumberField.RingOfIntegers K) K)).map
            (NumberField.AdelicLevel.archEval K w)).ne_zero
    · rw [NumberField.AdelicLevel.glArch_apply, h00]
    · rw [NumberField.AdelicLevel.glArch_apply, h01]
      rfl
    · rw [NumberField.AdelicLevel.glArch_apply, h10]
      rfl
    · rw [NumberField.AdelicLevel.glArch_apply, h11]
  have hfin : NumberField.AdelicHeight.finHeight K (NumberField.AdelicLevel.glFin
        (NumberField.RingOfIntegers K) K s * NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers K) K g)
      = NumberField.AdelicHeight.finHeight K (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers K) K g) := by
    unfold NumberField.AdelicHeight.finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_shape_mul (z := ζ.2 v) ?_ ?_ ?_ ?_ ?_
      (NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers K) K v (NumberField.AdelicLevel.glFin
            (NumberField.RingOfIntegers K) K g))
    · exact ((hζ.map (RingHom.snd (NumberField.InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing
          (NumberField.RingOfIntegers K) K))).map
        (NumberField.AdelicLevel.finAdeleEval (NumberField.RingOfIntegers K) K v)).ne_zero
    · rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply, h00]
    · rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply, h01]
      rfl
    · rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply, h10]
      rfl
    · rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply, h11]
  rw [harch, hfin]

theorem adelicHeight_centralScalar_mul (z : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.centralScalar (NumberField.RingOfIntegers K) K z * g)
      = NumberField.AdelicHeight.adelicHeight K g := by
  have hcoe : ((AutomorphicForm.centralScalar (NumberField.RingOfIntegers K) K z : AutomorphicForm.AdelicGL2
        (NumberField.RingOfIntegers K) K) :
      Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) =
            Matrix.scalar (Fin 2) (z : NumberField.AdeleRing (NumberField.RingOfIntegers K) K) := rfl
  refine adelicHeight_scalar_shape_mul K (ζ := (z : NumberField.AdeleRing
        (NumberField.RingOfIntegers K) K)) ?_ ?_ ?_ ?_ g <;>
    simp [hcoe, Matrix.scalar_apply]

end S24HeightFurniture

namespace S24

open AutomorphicForm

theorem glue_isFiniteMeasure_pins_ν (K : Type) [Field K] [NumberField K] (ΦK : Set (AdelicGL2 (𝓞 K) K)) :
    @IsFiniteMeasure _ (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS
      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν := by
  haveI := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox K
  show IsFiniteMeasure (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
  infer_instance

theorem continuous_unipotentGL2_adele (K : Type) [Field K] [NumberField K] :
    Continuous fun x : AdeleRing (𝓞 K) K => (AutomorphicForm.unipotentGL2 x : AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [AutomorphicForm.unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 K) K,
        (((AutomorphicForm.unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          !![1, -x; 0, 1] :=
      fun x => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem glue_measurable_unipotentGL2 (K : Type) [Field K] [NumberField K] (ΦK : Set (AdelicGL2 (𝓞 K) K)) :
    @Measurable _ _ (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _
      (fun t : AdeleRing (𝓞 K) K => AutomorphicForm.unipotentGL2 t) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  exact (continuous_unipotentGL2_adele K).measurable

theorem glue_unipotentGL2_adelicBox_relativelyCompact (K : Type) [Field K] [NumberField K]
    (ΦK : Set (AdelicGL2 (𝓞 K) K)) :
    ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧
      ∀ᵐ q ∂((productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν), (fun t : AdeleRing (𝓞 K) K => AutomorphicForm.unipotentGL2 t) q ∈ C := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset K
  refine ⟨(fun t : AdeleRing (𝓞 K) K => (AutomorphicForm.unipotentGL2 t : AdelicGL2 (𝓞 K) K)) '' C,
    hC.image (continuous_unipotentGL2_adele K), ?_⟩
  show ∀ᵐ q ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)),
    AutomorphicForm.unipotentGL2 q ∈ (fun t : AdeleRing (𝓞 K) K => (AutomorphicForm.unipotentGL2 t : AdelicGL2 (𝓞 K) K)) '' C
  rw [ProbabilityTheory.cond]
  have hp : ∀ᵐ q ∂((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)),
      AutomorphicForm.unipotentGL2 q ∈
        (fun t : AdeleRing (𝓞 K) K => (AutomorphicForm.unipotentGL2 t : AdelicGL2 (𝓞 K) K)) '' C := by
    filter_upwards [ae_restrict_mem (NumberField.AdelicBox.measurableSet_adelicBox K)] with q hq
    exact ⟨q, hsub hq, rfl⟩
  exact Measure.smul_absolutelyContinuous.ae_le hp

theorem glue_adelicHeight_centralScalar_mul (K : Type) [Field K] [NumberField K]
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.centralScalar (𝓞 K) K z * g) =
      NumberField.AdelicHeight.adelicHeight K g :=
  S24HeightFurniture.adelicHeight_centralScalar_mul K z g

end S24

open AutomorphicForm

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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          tabs n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
        (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) f faK ff
          (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else fSK v) →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tysK f →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
        Filter.Tendsto (fun R : ℝ =>
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y => AutomorphicForm.adelicKernel K f x y)
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          (R : ℂ) * s g) Filter.atTop (nhds (
          ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc +
          ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)))  := by
  obtain ⟨tabs, htabs, cs, hsum, heis, hmain⟩ :=
    AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK
      hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK faK fSK X hXc hX
  refine ⟨tabs, htabs, cs, hsum, heis, ?_⟩
  intro T hTd hT2 ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs
  obtain ⟨Λ, hΛ, s, hs⟩ := hmain T hTd hT2 ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs
  refine ⟨Λ, hΛ, s, ?_⟩
  intro ks js f hf hfc ff hfact hbi harch g hg
  have key := hs ks js f hf hfc ff hfact hbi harch g hg
  refine key.congr' (Filter.Eventually.of_forall fun R => ?_)
  have hfold := fun x : AdelicGL2 (𝓞 K) K =>
    (@AutomorphicForm.integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
      K _ _ _ _ νZK _ ΩK hΩK ξK hξc hξt f hf hfc _
      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS
      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
      (S24.glue_isFiniteMeasure_pins_ν K ΦK)
      (fun t => AutomorphicForm.unipotentGL2 t) (S24.glue_measurable_unipotentGL2 K ΦK)
      (S24.glue_unipotentGL2_adelicBox_relativelyCompact K ΦK)
      (NumberField.AdelicHeight.adelicHeight K) (S24.glue_adelicHeight_centralScalar_mul K)
      (Real.exp R) x x).2
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => (hfold x).symm)]

end S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul (solution)
