-- Prove2me | solution 1 for AutomorphicForm.exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/44420d7b-aee2-5328-885c-b6e814f5e59f

import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Theorems.Thm_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt"
p2m_attr_erase "simp" "LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

open scoped Classical
open IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K]

theorem norm_diag_eq_one_of_isRowIsometry {L : Type*} [NormedField L] (k : GL (Fin 2) L)
    (hk : AutomorphicForm.WindowedSiegel.IsRowIsometry k) (h10 : (k : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hk
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have := hrow 0 1
    rw [h10] at this
    simp only [zero_mul, one_mul, zero_add, mul_zero, norm_zero, norm_one] at this
    have h0 : 0 ≤ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ := norm_nonneg _
    nlinarith
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

theorem norm_eq_one_of_mul_eq_one (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K)
    (hxy : x * y = 1) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) : ‖x‖ = 1 := by
  apply le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hx)
  apply Valued.toNormedField.one_le_norm_iff.mpr
  have h := congrArg Valued.v hxy
  rw [map_mul, map_one] at h
  by_contra hlt
  push_neg at hlt
  have : Valued.v x * Valued.v y < 1 := mul_lt_one_of_lt_of_le hlt hy
  rw [h] at this
  exact lt_irrefl _ this

theorem distribHaarChar_borelDiag_eq_one (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K)
    (hβK : β ∈ adelicMaximalCompact K) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagFst ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 ∧
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagSnd ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hβ

  have harch : ∀ w : InfinitePlace K,
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ = 1 ∧
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ = 1 := by
    intro w
    have hk := hβK.2 w
    have h := norm_diag_eq_one_of_isRowIsometry (archComponent K w (glArch (𝓞 K) K β)) hk (by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w = 0
      rw [NumberField.AdelicLevel.glArch_apply, h10]; rfl)
    have e0 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    have e1 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    rw [e0, e1] at h
    exact h

  have hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Fin 2),
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v‖ = 1 := by
    intro v i
    have hle := AutomorphicForm.valued_finComponent_apply_le_one hβK v i i

    have ex : ((finComponent (𝓞 K) K v (glFin (𝓞 K) K β) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    have ey : (((finComponent (𝓞 K) K v (glFin (𝓞 K) K β))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [← map_inv, ← map_inv, NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    rw [ex] at hle; rw [ey] at hle

    have hprod : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) = 1 := by
      fin_cases i
      · exact congrArg Units.val (mul_inv_cancel (borelDiagFst (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
      · exact congrArg Units.val (mul_inv_cancel (borelDiagSnd (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
    have hprodv : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v = 1 := by
      have := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) hprod
      first
        | simpa using this
        | (have h' := this; simp at h' ⊢; exact h')
        | (have h' := this; simp at h'; exact h')
        | exact this
        | (simpa [Function.comp_def] using this)
    exact norm_eq_one_of_mul_eq_one v _ _ hprodv hle.1 hle.2
  constructor
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).1, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 0, one_mul]
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).2, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 1, one_mul]

end Ws31.SectionExt

end

noncomputable section

namespace Ws31
namespace AVG

variable (F : Type) [Field F] [NumberField F]

abbrev BK : Subgroup (AdelicGL2 (𝓞 F) F) := adelicBorel (𝓞 F) F ⊓ adelicMaximalCompact F

theorem isClosed_adelicBorel : IsClosed ((adelicBorel (𝓞 F) F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
  have : ((adelicBorel (𝓞 F) F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) =
      (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact (isClosed_singleton).preimage (Continuous.matrix_elem Units.continuous_val 1 0)

theorem isCompact_BK : IsCompact ((BK F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
  show IsCompact (((adelicBorel (𝓞 F) F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) ∩
      ((adelicMaximalCompact F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)))
  exact (AutomorphicForm.isCompact_adelicMaximalCompact F).inter_left (isClosed_adelicBorel F)

scoped instance : CompactSpace ↥(BK F) := isCompact_iff_compactSpace.mp (isCompact_BK F)

scoped instance : MeasurableSpace ↥(BK F) := borel _
scoped instance : BorelSpace ↥(BK F) := ⟨rfl⟩

def haarBK : Measure ↥(BK F) :=
  MeasureTheory.Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

scoped instance : (haarBK F).IsHaarMeasure := by
  unfold haarBK; exact MeasureTheory.Measure.isHaarMeasure_haarMeasure _

scoped instance : IsProbabilityMeasure (haarBK F) :=
  ⟨by unfold haarBK; exact MeasureTheory.Measure.haarMeasure_self⟩

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem BK_borel (b : ↥(BK F)) : (b : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := b.2.1
theorem BK_cpt (b : ↥(BK F)) : (b : AdelicGL2 (𝓞 F) F) ∈ adelicMaximalCompact F := b.2.2

def eta (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b : ↥(BK F)) : ℂ :=
  ((etaFst μ α hα 0 (borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩) : ℂˣ) : ℂ) *
    ((etaSnd ν α hα 0 (borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩) : ℂˣ) : ℂ)

theorem eta_mul (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b b' : ↥(BK F)) :
    eta α hα μ ν (b * b') = eta α hα μ ν b * eta α hα μ ν b' := by
  unfold eta
  have h1 : (⟨((b * b' : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel (b * b')⟩ : ↥(adelicBorel (𝓞 F) F)) =
      ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ * ⟨(b' : AdelicGL2 (𝓞 F) F), BK_borel b'⟩ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

theorem eta_one (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : eta α hα μ ν 1 = 1 := by
  unfold eta
  have h1 : (⟨((1 : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel 1⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := rfl
  rw [h1, map_one, map_one, map_one, map_one, Units.val_one, mul_one]

theorem eta_ne_zero (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b : ↥(BK F)) : eta α hα μ ν b ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

theorem eta_inv (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b : ↥(BK F)) : eta α hα μ ν b⁻¹ = (eta α hα μ ν b)⁻¹ := by
  have := eta_mul α hα μ ν b b⁻¹
  rw [mul_inv_cancel, eta_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

def avg (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : ↥(adelicMaximalCompact F) → ℂ)
    (k : ↥(adelicMaximalCompact F)) : ℂ :=
  ∫ b : ↥(BK F), eta α hα μ ν b * m (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩⁻¹ * k) ∂(haarBK F)

theorem avg_mul (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : ↥(adelicMaximalCompact F) → ℂ)
    (b₀ : ↥(BK F)) (k : ↥(adelicMaximalCompact F)) :
    avg α hα μ ν m (⟨(b₀ : AdelicGL2 (𝓞 F) F), BK_cpt b₀⟩ * k) = eta α hα μ ν b₀ * avg α hα μ ν m k := by
  unfold avg
  rw [← integral_const_mul]

  have h := MeasureTheory.integral_mul_left_eq_self
    (μ := haarBK F) (fun b : ↥(BK F) => eta α hα μ ν b * m (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩⁻¹ *
      (⟨(b₀ : AdelicGL2 (𝓞 F) F), BK_cpt b₀⟩ * k))) b₀
  rw [← h]
  congr 1
  funext b
  rw [eta_mul, mul_assoc]
  congr 2
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem avg_mul_right_eq (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : ↥(adelicMaximalCompact F) → ℂ)
    (u k : ↥(adelicMaximalCompact F)) (hu : ∀ k' : ↥(adelicMaximalCompact F), m (k' * u) = m k') :
    avg α hα μ ν m (k * u) = avg α hα μ ν m k := by
  unfold avg
  congr 1; funext b
  rw [← mul_assoc, hu]

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem continuous_borelDiagFst_BK :
    Continuous fun b : ↥(BK F) => (borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) := by
  have hval : ∀ b : ↥(BK F), ((borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := fun b => rfl
  have hinv : ∀ b : ↥(BK F), (((borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F) 0 0 := by
    intro b
    have : (borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ = borelDiagFst ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩ := by
      rw [← map_inv]; rfl
    rw [this]; rfl
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun b : ↥(BK F) => ((borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp_rw [hval]
    exact Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) 0 0
  · show Continuous fun b : ↥(BK F) => (((borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp_rw [hinv]
    exact Continuous.matrix_elem (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)) 0 0

theorem continuous_borelDiagSnd_BK :
    Continuous fun b : ↥(BK F) => (borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) := by
  have hval : ∀ b : ↥(BK F), ((borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := fun b => rfl
  have hinv : ∀ b : ↥(BK F), (((borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F) 1 1 := by
    intro b
    have : (borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ = borelDiagSnd ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩ := by
      rw [← map_inv]; rfl
    rw [this]; rfl
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun b : ↥(BK F) => ((borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp_rw [hval]
    exact Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) 1 1
  · show Continuous fun b : ↥(BK F) => (((borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp_rw [hinv]
    exact Continuous.matrix_elem (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)) 1 1

theorem continuous_eta (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)) :
    Continuous (eta α hα μ ν : ↥(BK F) → ℂ) := by
  unfold eta
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  refine ((hμc.comp continuous_borelDiagFst_BK).mul ?_).mul ((hνc.comp continuous_borelDiagSnd_BK).mul ?_)
  · refine Continuous.cpow ?_ continuous_const ?_
    · exact Complex.continuous_ofReal.comp (hαc.comp continuous_borelDiagFst_BK)
    · intro b; left; exact_mod_cast hα _
  · refine Continuous.cpow ?_ continuous_const ?_
    · exact Complex.continuous_ofReal.comp (hαc.comp continuous_borelDiagSnd_BK)
    · intro b; left; exact_mod_cast hα _

theorem continuous_avg (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (m : ↥(adelicMaximalCompact F) → ℂ) (hm : Continuous m) :
    Continuous (avg α hα μ ν m) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := inferInstance
  haveI : FirstCountableTopology ↥(adelicMaximalCompact F) := TopologicalSpace.Subtype.firstCountableTopology _
  unfold avg
  have hF : Continuous (fun p : ↥(adelicMaximalCompact F) × ↥(BK F) =>
      eta α hα μ ν p.2 * m (⟨(p.2 : AdelicGL2 (𝓞 F) F), BK_cpt p.2⟩⁻¹ * p.1)) := by
    refine ((continuous_eta α hα hαc μ ν hμc hνc).comp continuous_snd).mul (hm.comp ?_)
    refine Continuous.mul (Continuous.inv ?_) continuous_fst
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _
  have := continuous_parametric_integral_of_continuous (μ := haarBK F)
    (f := fun (k : ↥(adelicMaximalCompact F)) (b : ↥(BK F)) =>
      eta α hα μ ν b * m (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩⁻¹ * k)) hF isCompact_univ
  simpa only [Measure.restrict_univ] using this

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem integrable_BK_of_continuous (f : ↥(BK F) → ℂ) (hf : Continuous f) : Integrable f (haarBK F) :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem avg_add (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (f g : ↥(adelicMaximalCompact F) → ℂ) (hf : Continuous f) (hg : Continuous g) :
    avg α hα μ ν (f + g) = avg α hα μ ν f + avg α hα μ ν g := by
  funext k
  simp only [avg, Pi.add_apply, mul_add]
  have hc : ∀ (φ : ↥(adelicMaximalCompact F) → ℂ), Continuous φ →
      Continuous fun b : ↥(BK F) => eta α hα μ ν b * φ (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩⁻¹ * k) := by
    intro φ hφ
    refine (continuous_eta α hα hαc μ ν hμc hνc).mul (hφ.comp ?_)
    have h1 : Continuous fun b : ↥(BK F) => (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩ : ↥(adelicMaximalCompact F)) :=
      Continuous.subtype_mk continuous_subtype_val _
    exact h1.inv.mul continuous_const
  exact integral_add (integrable_BK_of_continuous _ (hc f hf)) (integrable_BK_of_continuous _ (hc g hg))

theorem avg_smul (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (c : ℂ) (f : ↥(adelicMaximalCompact F) → ℂ) :
    avg α hα μ ν (c • f) = c • avg α hα μ ν f := by
  funext k
  simp only [avg, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext b; ring

theorem avg_translate (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : ↥(adelicMaximalCompact F) → ℂ) (k₀ : ↥(adelicMaximalCompact F)) :
    (fun k => avg α hα μ ν m (k * k₀)) = avg α hα μ ν (fun k => m (k * k₀)) := by
  funext k
  simp only [avg, mul_assoc]

theorem avg_kFinite (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (m : ↥(adelicMaximalCompact F) → ℂ) (hm : Continuous m)
    (hW : ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
      ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m (k * k₀)) ∈ W) :
    ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
      ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => avg α hα μ ν m (k * k₀)) ∈ W := by
  classical
  obtain ⟨W, hWfd, hWm⟩ := hW

  let W₀ : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ) :=
    Submodule.span ℂ (Set.range fun k₀ : ↥(adelicMaximalCompact F) => fun k => m (k * k₀))
  have hW₀le : W₀ ≤ W := Submodule.span_le.mpr (by rintro _ ⟨k₀, rfl⟩; exact hWm k₀)
  haveI : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_of_le hW₀le
  have hcont : ∀ f ∈ W₀, Continuous f := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨k₀, rfl⟩; exact hm.comp (continuous_id.mul continuous_const)
    · exact continuous_const
    · intro f g _ _ hf hg; exact hf.add hg
    · intro c f _ hf; exact hf.const_smul c

  let P : W₀ →ₗ[ℂ] (↥(adelicMaximalCompact F) → ℂ) :=
    { toFun := fun f => avg α hα μ ν (f : ↥(adelicMaximalCompact F) → ℂ)
      map_add' := fun f g => by
        simpa using avg_add α hα hαc μ ν hμc hνc f g (hcont f f.2) (hcont g g.2)
      map_smul' := fun c f => by
        simpa using avg_smul α hα μ ν c f }
  refine ⟨LinearMap.range P, inferInstance, fun k₀ => ?_⟩
  rw [avg_translate]
  exact ⟨⟨fun k => m (k * k₀), Submodule.subset_span ⟨k₀, rfl⟩⟩, rfl⟩

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem diagOne_mul_borel (β : ↥(BK F)) (t : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.AdelicLevel.diagOne (t * (borelDiagFst ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)⁻¹ * (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)) * (β : AdelicGL2 (𝓞 F) F) =
      centralScalar (𝓞 F) F (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩) *
        unipotentGL2 ((((borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) *
            ((t * (borelDiagFst ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)⁻¹ * (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) *
          (((β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)) *
        NumberField.AdelicLevel.diagOne t := by
  set v₁ : (AdeleRing (𝓞 F) F)ˣ := (borelDiagFst ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩) with hv₁def
  set v₂ : (AdeleRing (𝓞 F) F)ˣ := (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩) with hv₂def
  set s : (AdeleRing (𝓞 F) F)ˣ := t * v₁⁻¹ * v₂ with hsdef
  have h10 : ((β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := BK_borel β
  have h00 : ((β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (v₁ : AdeleRing (𝓞 F) F) := rfl
  have h11 : ((β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (v₂ : AdeleRing (𝓞 F) F) := rfl
  have hv₁ : ((v₁ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((v₁⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv₂ : ((v₂ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((v₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hs : ((s : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = ↑t * ↑v₁⁻¹ * ↑v₂ := by
    rw [hsdef, Units.val_mul, Units.val_mul]
  set β₀₁ := ((β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 with hβ₀₁
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, NumberField.AdelicLevel.diagOne_coe_apply, unipotentGL2_coe,
      NumberField.AdelicVolume.centralScalar_val, Matrix.diagonal, h10, h00, h11, ← hβ₀₁]
  · linear_combination (↑v₁ : AdeleRing (𝓞 F) F) * hs + (↑t * ↑v₂ : AdeleRing (𝓞 F) F) * hv₁
  · linear_combination (-(↑s : AdeleRing (𝓞 F) F) * β₀₁) * hv₂

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem slab_diagOne_borel (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (hZ : ∀ x, x ∈ Z) (ξ : ↥Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : AutomorphicForm.IsSlabProfile F Z ξ φ)
    (β : ↥(BK F)) (t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (NumberField.AdelicLevel.diagOne
        (t * (borelDiagFst ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)⁻¹ * (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩)) *
        ((β : AdelicGL2 (𝓞 F) F) * g)) =
      ((ξ ⟨borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩, hZ _⟩ : ℂˣ) : ℂ) * φ (NumberField.AdelicLevel.diagOne t * g) := by
  rw [← mul_assoc, diagOne_mul_borel β t, mul_assoc, mul_assoc]
  have := hφ.central_transform ⟨borelDiagSnd ⟨(β : AdelicGL2 (𝓞 F) F), BK_borel β⟩, hZ _⟩
  rw [this, hφ.unipotent_mul]

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have hp := NumberField.TateGlobal.ideleNorm_pos (F := F) 1

  have : NumberField.TateGlobal.ideleNorm F 1 * (NumberField.TateGlobal.ideleNorm F 1 - 1) = 0 := by linear_combination (-1 : ℝ) * h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact absurd h0 hp.ne'
  · linarith

theorem ideleNorm_inv (x : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F x⁻¹ = (NumberField.TateGlobal.ideleNorm F x)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) x⁻¹ x
  rw [inv_mul_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem enorm_integral_sq_le {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℂ) (hf : AEMeasurable f P) :
    ‖∫ x, f x ∂P‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂P := by
  have h1 : ‖∫ x, f x ∂P‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂P := enorm_integral_le_lintegral_enorm f
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hf.enorm aemeasurable_const (g := fun _ => (1 : ℝ≥0∞))
  simp only [mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_mul] at h2
  have h3 : (∫⁻ x, ‖f x‖ₑ ∂P) ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    simpa using h2
  calc ‖∫ x, f x ∂P‖ₑ ^ (2 : ℝ) ≤ (∫⁻ x, ‖f x‖ₑ ∂P) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂P := by rw [← ENNReal.rpow_mul]; norm_num

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

noncomputable section

namespace Ws31
namespace AVG

variable {F : Type} [Field F] [NumberField F]

theorem continuous_diagOne :
    Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (NumberField.AdelicLevel.diagOne t : AdelicGL2 (𝓞 F) F) := by
  have hval : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2),
      ((NumberField.AdelicLevel.diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
        Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] i j := fun t i j => rfl
  have hinv : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2),
      ((↑((NumberField.AdelicLevel.diagOne t : AdelicGL2 (𝓞 F) F)⁻¹) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) =
        Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] i j := by
    intro t i j; rw [← map_inv]; rfl
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · show Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      ((NumberField.AdelicLevel.diagOne a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
    simp only [hval]
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const
  · simp only [hinv]
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const

end Ws31.AVG
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31 P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.Ws31.AVG"
set_option synthInstance.maxHeartbeats 1600000 in
open Ws31.AVG Ws31.SectionExt in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (_hξt : ∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z,
        (z : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F → ξ z = 1)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (n : ℕ)
      (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ j, IsUnitaryChar (𝓞 F) F (μ j)) (_hμic : ∀ j, IsIdeleClassChar (𝓞 F) F (μ j))
      (_hμc : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ))
      (h : Fin n → ℝ → ℂ) (_hh : ∀ j, Continuous (h j))
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ) (_hmc : ∀ j, Continuous (m j))
      (_hmW : ∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W)
      (_hmsm : ∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k),
    ∃ (ν : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (u : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (ν j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (ν j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν j x : ℂˣ) : ℂ)) ∧
      (∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ j, Continuous (u j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => u j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u' : ↥(adelicMaximalCompact F)),
        (u' : AdelicGL2 (𝓞 F) F) ∈ V → (u' : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          u j (k * u') = u j k) ∧
      (∀ (j : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbK : b ∈ adelicMaximalCompact F)
        (k : ↥(adelicMaximalCompact F)),
        u j (⟨b, hbK⟩ * k) =
          ((etaFst (μ j) α hα 0 (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((etaSnd (ν j) α hα 0 (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ) *
            u j k) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) *
              u j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ≤
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by
  intro α hα Φ ξ _hξ _hξu _hξt φ _hφ D _hDm _hDF n μ _hμ _hμic _hμc h _hh m _hmc _hmW _hmsm
  classical

  let inclZ : (AdeleRing (𝓞 F) F)ˣ →* ↥(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z :=
    { toFun := fun z => ⟨z, show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) from Subgroup.mem_top z⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ν : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun j => (ξ.comp inclZ) * (μ j)⁻¹
  have hνapply : ∀ j z, ((ν j z : ℂˣ) : ℂ) = ((ξ (inclZ z) : ℂˣ) : ℂ) * (((μ j z : ℂˣ) : ℂ))⁻¹ := by
    intro j z; simp [ν, Units.val_inv_eq_inv_val]
  have hνu : ∀ j, IsUnitaryChar (𝓞 F) F (ν j) := by
    intro j z; rw [hνapply, norm_mul, norm_inv, _hξu, _hμ j z]; simp
  have hνic : ∀ j, IsIdeleClassChar (𝓞 F) F (ν j) := by
    intro j u
    apply Units.ext
    rw [hνapply, Units.val_one]
    have h1 : ξ (inclZ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u)) = 1 :=
      _hξt _ ⟨u, rfl⟩
    rw [h1, _hμic j u]; simp
  have hιc : Continuous inclZ := Continuous.subtype_mk continuous_id _
  have hνc : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν j x : ℂˣ) : ℂ) := by
    intro j
    have e1 : (fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν j x : ℂˣ) : ℂ)) =
        fun x => ((ξ (inclZ x) : ℂˣ) : ℂ) * (((μ j x : ℂˣ) : ℂ))⁻¹ := funext (hνapply j)
    rw [e1]
    exact Continuous.mul (Units.continuous_val.comp (_hξ.comp hιc)) ((_hμc j).inv₀ fun x => Units.ne_zero _)
  have hμν : ∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
      μ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z := by
    intro j z
    have : inclZ (z : (AdeleRing (𝓞 F) F)ˣ) = z := Subtype.ext rfl
    simp only [ν, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, this]
    rw [mul_comm, inv_mul_cancel_right]

  have hαI : ∀ x, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := fun x => rfl
  have hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ) := by
    simp_rw [hαI]; exact NumberField.TateGlobal.continuous_ideleNorm F

  let u : Fin n → ↥(adelicMaximalCompact F) → ℂ := fun j => avg α hα (μ j) (ν j) (m j)
  refine ⟨ν, u, hνu, hνic, hνc, hμν, fun j => continuous_avg α hα hαc (μ j) (ν j) (_hμc j) (hνc j) (m j) (_hmc j),
    fun j => avg_kFinite α hα hαc (μ j) (ν j) (_hμc j) (hνc j) (m j) (_hmc j) (_hmW j), fun j => ?_, ?_, ?_⟩
  ·
    obtain ⟨V, hV, hinv⟩ := _hmsm j
    exact ⟨V, hV, fun k u' hu'V hu'f => avg_mul_right_eq α hα (μ j) (ν j) (m j) u' k fun k' => hinv k' u' hu'V hu'f⟩
  ·
    intro j b hb hbK k
    have := avg_mul α hα (μ j) (ν j) (m j) ⟨b, ⟨hb, hbK⟩⟩ k
    exact this
  ·
    haveI hSC : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ :=
      (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box F F).1
    haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
      NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
    haveI : MeasurableMul₂ (AdeleRing (𝓞 F) F)ˣ := inferInstance
    haveI : (NumberField.Idele.idelicHaar F).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar F

    set ρ : Measure ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) :=
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
        (maximalCompactHaar F)) with hρ
    set G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ := fun p =>
      φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
        ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2 with hG
    set G' : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ := fun p =>
      φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
        ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * u j p.2 with hG'
    show eLpNorm G' 2 ρ ≤ eLpNorm G 2 ρ

    let v₁ : ↥(BK F) → (AdeleRing (𝓞 F) F)ˣ := fun b => borelDiagFst ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩
    let v₂ : ↥(BK F) → (AdeleRing (𝓞 F) F)ˣ := fun b => borelDiagSnd ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩
    let cb : ↥(BK F) → (AdeleRing (𝓞 F) F)ˣ := fun b => (v₁ b)⁻¹ * v₂ b
    let kb : ↥(BK F) → ↥(adelicMaximalCompact F) := fun b => ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_cpt b⁻¹⟩
    let ξb : ↥(BK F) → ℂ := fun b => ((ξ (inclZ (v₂ b)) : ℂˣ) : ℂ)
    let τ : ↥(BK F) → (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) :=
      fun b p => (p.1 * cb b, kb b * p.2)

    have hmod : ∀ b : ↥(BK F), NumberField.TateGlobal.ideleNorm F (v₁ b) = 1 ∧ NumberField.TateGlobal.ideleNorm F (v₂ b) = 1 :=
      fun b => Ws31.SectionExt.distribHaarChar_borelDiag_eq_one _ (BK_borel b⁻¹) (BK_cpt b⁻¹)
    have hcb1 : ∀ b, NumberField.TateGlobal.ideleNorm F (cb b) = 1 := by
      intro b
      show NumberField.TateGlobal.ideleNorm F ((v₁ b)⁻¹ * v₂ b) = 1
      rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, (hmod b).1, (hmod b).2]; norm_num
    have hξb1 : ∀ b, ‖ξb b‖ = 1 := fun b => _hξu _
    have hξb0 : ∀ b, ξb b ≠ 0 := fun b => norm_ne_zero_iff.mp (by rw [hξb1]; exact one_ne_zero)

    have hkey : ∀ (j : Fin n) (b : ↥(BK F)), eta α hα (μ j) (ν j) b = (ξb b)⁻¹ * ((μ j (cb b) : ℂˣ) : ℂ) := by
      intro j b

      have e1 : borelDiagFst ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ = (v₁ b)⁻¹ := by
        show _ = (borelDiagFst ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩)⁻¹
        rw [← map_inv]; congr 1
      have e2 : borelDiagSnd ⟨(b : AdelicGL2 (𝓞 F) F), BK_borel b⟩ = (v₂ b)⁻¹ := by
        show _ = (borelDiagSnd ⟨((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F), BK_borel b⁻¹⟩)⁻¹
        rw [← map_inv]; congr 1
      have hαv1 : ((α (v₁ b)⁻¹ : ℝˣ) : ℝ) = 1 := by rw [hαI, ideleNorm_inv, (hmod b).1, inv_one]
      have hαv2 : ((α (v₂ b)⁻¹ : ℝˣ) : ℝ) = 1 := by rw [hαI, ideleNorm_inv, (hmod b).2, inv_one]
      unfold eta
      rw [e1, e2, etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val,
        hαv1, hαv2]
      simp only [Complex.ofReal_one, Complex.one_cpow, mul_one]

      dsimp only [ξb, cb]
      rw [hνapply]
      simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp

    have hZ : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
        x ∈ (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z :=
      fun x => show x ∈ (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) from Subgroup.mem_top x

    have hkb : ∀ b : ↥(BK F), kb b = (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩ : ↥(adelicMaximalCompact F))⁻¹ :=
      fun b => Subtype.ext rfl
    have htorus : ∀ (b : ↥(BK F)) (p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)),
        φ (NumberField.AdelicLevel.diagOne (p.1 * cb b) * ((kb b * p.2 : ↥(adelicMaximalCompact F)) : AdelicGL2 (𝓞 F) F))
          = ξb b * φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) := by
      intro b p
      have := slab_diagOne_borel _ hZ ξ φ _hφ (b⁻¹) p.1 (p.2 : AdelicGL2 (𝓞 F) F)
      rw [Subgroup.coe_mul]
      show φ (NumberField.AdelicLevel.diagOne (p.1 * ((v₁ b)⁻¹ * v₂ b)) *
          (((b⁻¹ : ↥(BK F)) : AdelicGL2 (𝓞 F) F) * (p.2 : AdelicGL2 (𝓞 F) F))) = _
      rw [← mul_assoc p.1]
      exact this
    have hintegrand : ∀ (b : ↥(BK F)) (p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)),
        (ξb b)⁻¹ * G (τ b p) =
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) *
              (eta α hα (μ j) (ν j) b * m j ((⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩ : ↥(adelicMaximalCompact F))⁻¹ * p.2)) := by
      intro b p
      simp only [hG, τ]
      rw [htorus, mul_sub, ← mul_assoc, inv_mul_cancel₀ (hξb0 b), one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Units.val_mul, NumberField.TateGlobal.ideleNorm_mul, hcb1, mul_one, hkey, hkb]
      ring
    have hcontF : ∀ (j : Fin n) (k : ↥(adelicMaximalCompact F)), Continuous fun b : ↥(BK F) =>
        eta α hα (μ j) (ν j) b * m j ((⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩ : ↥(adelicMaximalCompact F))⁻¹ * k) := by
      intro j k
      refine (continuous_eta α hα hαc (μ j) (ν j) (_hμc j) (hνc j)).mul ((_hmc j).comp ?_)
      have h1 : Continuous fun b : ↥(BK F) => (⟨(b : AdelicGL2 (𝓞 F) F), BK_cpt b⟩ : ↥(adelicMaximalCompact F)) :=
        Continuous.subtype_mk continuous_subtype_val _
      exact h1.inv.mul continuous_const
    have hV : ∀ p, G' p = ∫ b, (ξb b)⁻¹ * G (τ b p) ∂(haarBK F) := by
      intro p
      simp_rw [hintegrand]
      rw [integral_sub (integrable_const _) (integrable_finset_sum _ fun j _ =>
        ((integrable_BK_of_continuous _ (hcontF j p.2)).const_mul _)), integral_const, probReal_univ, one_smul,
        integral_finset_sum _ fun j _ => ((integrable_BK_of_continuous _ (hcontF j p.2)).const_mul _)]
      simp only [hG', integral_const_mul]
      rfl

    haveI : SecondCountableTopology ↥(adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
    haveI : SecondCountableTopology ↥(BK F) := TopologicalSpace.Subtype.secondCountableTopology _
    haveI : SecondCountableTopology ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) := inferInstance
    haveI : BorelSpace ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) := Prod.borelSpace
    haveI : BorelSpace (((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) × ↥(BK F)) := Prod.borelSpace
    have hτc : ∀ b, Continuous (τ b) := fun b =>
      (continuous_fst.mul continuous_const).prodMk (continuous_const.mul continuous_snd)
    have hcbc : Continuous cb := by
      have h1 : Continuous fun b : ↥(BK F) => b⁻¹ := continuous_inv
      exact ((continuous_borelDiagFst_BK.comp h1).inv).mul (continuous_borelDiagSnd_BK.comp h1)
    have hkbc : Continuous kb :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_inv) _
    have hτc2 : Continuous fun q : ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) × ↥(BK F) => τ q.2 q.1 :=
      ((continuous_fst.comp continuous_fst).mul (hcbc.comp continuous_snd)).prodMk
        ((hkbc.comp continuous_snd).mul (continuous_snd.comp continuous_fst))
    have hGm : Measurable G := by
      have h1 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) :=
        _hφ.measurable.comp ((continuous_diagOne.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd)).measurable
      have h2 : ∀ j, Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2 := by
        intro j
        refine ((((_hμc j).comp continuous_fst).measurable.mul ?_).mul ((_hmc j).comp continuous_snd).measurable)
        exact (_hh j).measurable.comp (Real.measurable_log.comp
          ((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_fst).measurable)
      simp only [hG]
      exact h1.sub (Finset.measurable_sum _ fun j _ => h2 j)

    have hJ : ∀ p, ‖G' p‖ₑ ^ (2 : ℝ) ≤ ∫⁻ b, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂(haarBK F) := by
      intro p
      rw [hV p]
      have hmeas : AEMeasurable (fun b => (ξb b)⁻¹ * G (τ b p)) (haarBK F) := by
        refine (Measurable.mul ?_ (hGm.comp (hτc2.comp (continuous_const.prodMk continuous_id)).measurable)).aemeasurable
        exact ((Units.continuous_val.comp (_hξ.comp (hιc.comp (continuous_borelDiagSnd_BK.comp continuous_inv)))).measurable).inv
      refine (enorm_integral_sq_le (haarBK F) _ hmeas).trans (le_of_eq ?_)
      congr 1; funext b
      rw [enorm_mul, enorm_inv (hξb0 b), show ‖ξb b‖ₑ = 1 from by rw [← ofReal_norm_eq_enorm, hξb1]; simp, inv_one, one_mul]

    have hper : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F →
        ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)), G (γ * t, k) = G (t, k) := by
      rintro γ ⟨γ₀, rfl⟩ t k
      have hN : NumberField.TateGlobal.ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀) = 1 := by
        have h := NumberField.AdeleRing.distribHaarChar_algebraMap F γ₀
        have h' : ((distribHaarChar (AdeleRing (𝓞 F) F)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀) : ℝ≥0) : ℝ) = 1 := by
          exact_mod_cast h
        exact h'
      have hdiag : NumberField.AdelicLevel.diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ₀) =
          globalPoints (𝓞 F) F (NumberField.AdelicLevel.diagOne γ₀) := by
        apply Units.ext; ext i j
        rw [NumberField.AdelicLevel.diagOne_coe_apply, globalPoints_apply, NumberField.AdelicLevel.diagOne_coe_apply]
        fin_cases i <;> fin_cases j <;> simp
      have hmem : NumberField.AdelicLevel.diagOne γ₀ ∈ borelSubgroup F := by
        show (NumberField.AdelicLevel.diagOne γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        rw [NumberField.AdelicLevel.diagOne_coe_apply]; simp
      simp only [hG]
      rw [map_mul, mul_assoc, hdiag, _hφ.borel_mul _ hmem]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, _hμic j γ₀, one_mul, NumberField.TateGlobal.ideleNorm_mul, hN, one_mul]
    have hInv : ∀ b, ∫⁻ p, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂ρ = ∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂ρ := by
      intro b
      have := NumberField.Idele.lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
        F D _hDm _hDF (fun p => ‖G p‖ₑ ^ (2 : ℝ)) (hGm.enorm.pow_const _)
        (fun γ hγ t k => by simp only [hper γ hγ t k]) (cb b) (hcb1 b) (kb b)
      simpa only [hρ] using this
    have hT : ∫⁻ p, (∫⁻ b, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂(haarBK F)) ∂ρ = ∫⁻ b, (∫⁻ p, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂ρ) ∂(haarBK F) := by
      refine lintegral_lintegral_swap ?_
      exact ((hGm.comp hτc2.measurable).enorm.pow_const _).aemeasurable
    have hmain : ∫⁻ p, ‖G' p‖ₑ ^ (2 : ℝ) ∂ρ ≤ ∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂ρ := by
      calc ∫⁻ p, ‖G' p‖ₑ ^ (2 : ℝ) ∂ρ ≤ ∫⁻ p, (∫⁻ b, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂(haarBK F)) ∂ρ := lintegral_mono hJ
        _ = ∫⁻ b, (∫⁻ p, ‖G (τ b p)‖ₑ ^ (2 : ℝ) ∂ρ) ∂(haarBK F) := hT
        _ = ∫⁻ b, (∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂ρ) ∂(haarBK F) := by simp_rw [hInv]
        _ = ∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂ρ := by rw [lintegral_const, measure_univ, mul_one]

    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow hmain (by norm_num)

end
end S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
end P2MW
export P2MW.S_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile (solution)
