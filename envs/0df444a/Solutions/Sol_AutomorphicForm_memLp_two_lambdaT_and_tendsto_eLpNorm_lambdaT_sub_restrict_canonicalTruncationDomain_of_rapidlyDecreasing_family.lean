-- Prove2me | solution 1 for AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b4fe3aac-dcd0-58d5-8309-946df165986b

import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1L2ContFamily

open MeasureTheory Set NumberField IsDedekindDomain Filter
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicHeight

open scoped NNReal ENNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
set_option quotPrecheck false in

local notation "αF" => (MonoidHom.toHomUnits
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))) :
    (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)

section Height

variable {F}

variable (F) in

theorem exists_borel_mul_maximalCompact_eq (g : AdelicGL2 (𝓞 F) F) :
    ∃ (b : ↥(adelicBorel (𝓞 F) F)) (k : ↥(adelicMaximalCompact F)),
      g = (b : AdelicGL2 (𝓞 F) F) * (k : AdelicGL2 (𝓞 F) F) := by
  obtain ⟨b, k, hb, hk₁, hk₂, hg⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  exact ⟨⟨b, hb⟩, ⟨k, mem_adelicMaximalCompact_iff.2 ⟨hk₁, hk₂⟩⟩, hg⟩

def hgt (b : ↥(adelicBorel (𝓞 F) F)) : ℝ :=
  ((αF (borelDiagFst b) : ℝˣ) : ℝ) / ((αF (borelDiagSnd b) : ℝˣ) : ℝ)

theorem hgt_pos (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (b : ↥(adelicBorel (𝓞 F) F)) : 0 < hgt b :=
  div_pos (hα _) (hα _)

theorem adelicHeight_borel_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (b : ↥(adelicBorel (𝓞 F) F))
    (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F ((b : AdelicGL2 (𝓞 F) F) * g) = hgt b * adelicHeight F g := by
  have h := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα (1 / 2) b b.2 g
  have e1 : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [e1, Complex.cpow_one, etaFst_apply, etaSnd_apply, MonoidHom.one_apply,
    one_mul, cpowChar_apply_val, Complex.cpow_neg_one] at h
  apply Complex.ofReal_injective
  rw [h]
  unfold hgt
  push_cast
  ring

theorem adelicHeight_of_mem_maximalCompact {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    adelicHeight F k = 1 := by
  rw [adelicHeight_eq_archHeight_of_mem (glFin_mem_finiteIntegralGL2 hk)]
  have h := archHeight_mul_rowIsometry F 1 (k := glArch (𝓞 F) F k) (isRowIsometry_archComponent hk)
  rwa [one_mul, archHeight_one] at h

theorem adelicHeight_borel_mul_maximalCompact (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    (b : ↥(adelicBorel (𝓞 F) F)) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    adelicHeight F ((b : AdelicGL2 (𝓞 F) F) * k) = hgt b := by
  rw [adelicHeight_borel_mul hα, adelicHeight_of_mem_maximalCompact hk, mul_one]

end Height

section Continuation

theorem eqOn_of_eq_on_halfPlane {O : Set ℂ} (hOc : IsPreconnected O)
    (hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f O) (hg : AnalyticOnNhd ℂ g O)
    (h : ∀ s : ℂ, 1 / 2 < s.re → f s = g s) : EqOn f g O := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 / 2 : ℝ) < (1 : ℂ).re
    norm_num
  have hev : f =ᶠ[𝓝 (1 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds h1) fun s hs => h s hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hOc (hOhalf h1) hev

end Continuation

section Automorphy

variable {F}

theorem isPrincipalTrivial_haarMod : IsPrincipalTrivial (R := 𝓞 F) (K := F) αF := by
  intro a
  apply Units.ext
  rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, Units.val_one]
  have e : Units.map ((algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom) a
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) a := Units.ext rfl
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  rw [e] at h
  rw [h, map_one]

private theorem _root_.R1L2ContFamily.apply_globalPoints_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (s : ℂ) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) f)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    f (globalPoints (𝓞 F) F γ * g) = f g := by
  have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hγ
  rw [hf _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ, borelDiagSnd_globalPoints (𝓞 F) F hγ,
    etaFst_isIdeleClassChar hμic isPrincipalTrivial_haarMod s _,
    etaSnd_isIdeleClassChar hνic isPrincipalTrivial_haarMod s _]
  simp

p2m_export "R1L2ContFamily" "apply_globalPoints_mul"

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    g * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * g := by
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) 𝔸) * (Matrix.scalar (Fin 2) (z : 𝔸))
    = (Matrix.scalar (Fin 2) (z : 𝔸)) * (g : Matrix (Fin 2) (Fin 2) 𝔸)
  exact ((Matrix.scalar_commute (z : 𝔸) (Commute.all _) (g : Matrix (Fin 2) (Fin 2) 𝔸)).eq).symm

private theorem _root_.R1L2ContFamily.apply_mul_centralScalar (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (s : ℂ) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) f)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    f (g * centralScalar (𝓞 F) F z) = ((μ z * ν z : ℂˣ) : ℂ) * f g := by
  rw [mul_centralScalar_comm, isInducedSection_centralScalar_mul hf, ← Units.val_mul, etaFst_mul_etaSnd]

p2m_export "R1L2ContFamily" "apply_mul_centralScalar"

theorem pseudoEisenstein_mul_centralScalar (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (s : ℂ) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) f)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F f (g * centralScalar (𝓞 F) F z) = ((μ z * ν z : ℂˣ) : ℂ) * pseudoEisenstein F f g := by
  rw [pseudoEisenstein_apply, pseudoEisenstein_apply, mul_add, ← tsum_mul_left, apply_mul_centralScalar hα s hf]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, apply_mul_centralScalar hα s hf]

theorem pseudoEisenstein_globalPoints_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) f) (hfc : Continuous f)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F f (globalPoints (𝓞 F) F γ * g) = pseudoEisenstein F f g := by
  have hB : ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F b * y) = f y :=
    fun b hb y => apply_globalPoints_mul hα hμic hνic s hf hb y
  have hsum : Summable fun ξ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g) :=
    (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα μ ν hμ hν s hs f hf hfc g).of_norm
  exact (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F
    f hB g hsum γ).2

end Automorphy

section Family

variable {F}

structure FamilyData (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (O : Set ℂ) (Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ) : Prop where
  hμ : IsUnitaryChar (𝓞 F) F μ
  hν : IsUnitaryChar (𝓞 F) F ν
  hμic : IsIdeleClassChar (𝓞 F) F μ
  hνic : IsIdeleClassChar (𝓞 F) F ν
  hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) (φ s)
  hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)
  hO : IsOpen O
  hOc : IsPreconnected O
  hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O
  hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O
  hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ)
  hE : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F, Ec s g = pseudoEisenstein F (φ s) g

namespace FamilyData

theorem continuous_section {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (s : ℂ) : Continuous (φ s) :=
  D.hφjc.comp (Continuous.prodMk_right s)

theorem continuous_apply {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) {s : ℂ} (hs : s ∈ O) : Continuous (Ec s) := by
  have h : ContinuousOn (fun g : AdelicGL2 (𝓞 F) F => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F)) Set.univ :=
    (Continuous.prodMk_right s).continuousOn
  have h2 := D.hEjc.comp h (fun g _ => ⟨hs, Set.mem_univ _⟩)
  exact continuousOn_univ.1 h2

theorem apply_globalPoints_mul {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F)
    (g : AdelicGL2 (𝓞 F) F) {s : ℂ} (hs : s ∈ O) : Ec s (globalPoints (𝓞 F) F γ * g) = Ec s g := by
  refine eqOn_of_eq_on_halfPlane D.hOc D.hOhalf (D.hEa _) (D.hEa _) (fun s' hs' => ?_) hs
  rw [D.hE s' hs', D.hE s' hs']
  exact pseudoEisenstein_globalPoints_mul hα D.hμ D.hν D.hμic D.hνic hs' (D.hφ s') (D.continuous_section s') hγ g

theorem apply_mul_centralScalar {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (z : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) {s : ℂ} (hs : s ∈ O) :
    Ec s (g * centralScalar (𝓞 F) F z) = ((μ z * ν z : ℂˣ) : ℂ) * Ec s g := by
  have han : AnalyticOnNhd ℂ (fun s => ((μ z * ν z : ℂˣ) : ℂ) * Ec s g) O :=
    (analyticOnNhd_const).mul (D.hEa g)
  refine eqOn_of_eq_on_halfPlane D.hOc D.hOhalf (D.hEa _) han (fun s' hs' => ?_) hs
  show Ec s' (g * centralScalar (𝓞 F) F z) = ((μ z * ν z : ℂˣ) : ℂ) * Ec s' g
  rw [D.hE s' hs', D.hE s' hs']
  exact pseudoEisenstein_mul_centralScalar hα s' (D.hφ s') z g

theorem norm_apply_mul_centralScalar {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (z : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) {s : ℂ} (hs : s ∈ O) :
    ‖Ec s (g * centralScalar (𝓞 F) F z)‖ = ‖Ec s g‖ := by
  rw [D.apply_mul_centralScalar z g hs, norm_mul, Units.val_mul, norm_mul, D.hμ z, D.hν z, one_mul, one_mul]

theorem exists_bound_on_compact_mul {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) {C : Set ℂ} (hC : IsCompact C) (hCO : C ⊆ O)
    {Kc Tc : Set (AdelicGL2 (𝓞 F) F)} (hKc : IsCompact Kc) (hTc : IsCompact Tc) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ C, ∀ k ∈ Kc, ∀ y ∈ Tc, ‖Ec s (k * y)‖ ≤ B := by
  have hKT : IsCompact ((fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) '' (Kc ×ˢ Tc)) :=
    (hKc.prod hTc).image continuous_mul
  have hprod : IsCompact (C ×ˢ ((fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) '' (Kc ×ˢ Tc))) :=
    hC.prod hKT
  have hsub : C ×ˢ ((fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) '' (Kc ×ˢ Tc))
      ⊆ O ×ˢ Set.univ := Set.prod_mono hCO (Set.subset_univ _)
  obtain ⟨B, hB⟩ := hprod.exists_bound_of_continuousOn (D.hEjc.mono hsub)
  refine ⟨max B 0, le_max_right _ _, fun s hs k hk y hy => ?_⟩
  exact (hB (s, k * y) ⟨hs, ⟨(k, y), ⟨hk, hy⟩, rfl⟩⟩).trans (le_max_left _ _)

end FamilyData

scoped instance isFiniteMeasure_cond_adelicBox :
    IsFiniteMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  infer_instance

theorem measurable_lambdaT_of_continuous {E : AdelicGL2 (𝓞 F) F → ℂ} (hE : Continuous E) (T : ℝ) :
    Measurable (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (adelicHeight F) T E) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hCT : StronglyMeasurable (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) E) := by
    have hc2 : Continuous fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => E (unipotentGL2 p.2 * p.1) :=
      hE.comp ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul continuous_fst)
    have h := hc2.stronglyMeasurable
    exact h.integral_prod_right'
  have hH : MeasurableSet (highSet (adelicHeight F) T) :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight F).measurable
  exact hE.measurable.sub (hCT.measurable.indicator hH)

theorem continuousWithinAt_constantTerm {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (x : AdelicGL2 (𝓞 F) F) {s₀ : ℂ}
    (hs₀ : s₀ ∈ O) :
    ContinuousWithinAt (fun s => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (Ec s) x) O s₀ := by

  obtain ⟨r, hr, hrO⟩ := (Metric.nhds_basis_closedBall.mem_iff).1 (D.hO.mem_nhds hs₀)
  have hCc : IsCompact (Metric.closedBall s₀ r) := isCompact_closedBall s₀ r

  obtain ⟨Cb, hCb, hboxCb⟩ := exists_isCompact_adelicBox_subset F
  have hKc : IsCompact ((fun t : AdeleRing (𝓞 F) F => unipotentGL2 t * x) '' Cb) :=
    hCb.image (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)
  obtain ⟨B, hB0, hB⟩ := D.exists_bound_on_compact_mul hCc hrO hKc (isCompact_singleton (x := (1 : AdelicGL2 (𝓞 F) F)))
  have hmemC : Metric.closedBall s₀ r ∈ 𝓝[O] s₀ :=
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds s₀ hr)
  unfold constantTerm constantTermIntegrand
  refine MeasureTheory.continuousWithinAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((D.continuous_apply hs).comp
      (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hmemC] with s hs
    have hae : ∀ᵐ t ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), t ∈ adelicBox F :=
      ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
    filter_upwards [hae] with t ht
    have := hB s hs (unipotentGL2 t * x) ⟨t, hboxCb ht, rfl⟩ 1 rfl
    simpa using this
  · refine Filter.Eventually.of_forall fun t => ?_
    exact ((D.hEa (unipotentGL2 t * x) s₀ hs₀).continuousAt).continuousWithinAt

theorem continuousWithinAt_lambdaT {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (T : ℝ) (x : AdelicGL2 (𝓞 F) F) {s₀ : ℂ}
    (hs₀ : s₀ ∈ O) :
    ContinuousWithinAt (fun s => lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (adelicHeight F) T (Ec s) x) O s₀ := by
  have hEcont : ContinuousWithinAt (fun s => Ec s x) O s₀ :=
    ((D.hEa x s₀ hs₀).continuousAt).continuousWithinAt
  by_cases hx : T < adelicHeight F x
  · simp only [lambdaT_apply_of_lt _ _ hx]
    exact hEcont.sub (continuousWithinAt_constantTerm D x hs₀)
  · simp only [lambdaT_apply_of_le _ _ (not_lt.1 hx)]
    exact hEcont

end Family

section Slab

variable {F}

theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (ht : MeasurableSet t) (hst : s ⊆ t) (h : NullMeasurableSet s (μ.restrict t)) : NullMeasurableSet s μ := by
  obtain ⟨s', hs'm, hs'⟩ := h
  refine ⟨s' ∩ t, hs'm.inter ht, ?_⟩
  have h2 : ∀ᵐ x ∂μ, x ∈ t → (x ∈ s) = (x ∈ s') := (ae_restrict_iff' ht).mp hs'
  filter_upwards [h2] with x hx
  by_cases hxt : x ∈ t
  · have := hx hxt
    show (x ∈ s) = (x ∈ s' ∩ t)
    rw [this]; simp [hxt]
  · have hxs : x ∉ s := fun h => hxt (hst h)
    show (x ∈ s) = (x ∈ s' ∩ t)
    simp [hxs, hxt]

variable (F) in

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab F α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det F).measurable measurableSet_Icc

theorem nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {Φ : Set (AdelicGL2 (𝓞 F) F)} (hΦs : Φ ⊆ slab F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧ adelicGLHaar (Fin 2) (𝓞 F) F Φ < ⊤ := by
  refine ⟨nullMeasurableSet_of_restrict _ (measurableSet_slab α β) hΦs hΦ.nullMeasurableSet, ?_⟩
  have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    F α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_self_of_subset_left (show Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F
    (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} from hΦs)] at h

end Slab

section Bound

variable {F}

def DecayHyp (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (O : Set ℂ) (Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
    IsCompact C → C ⊆ O → IsCompact Ω → 0 < c' →
    ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
      ω ∈ Ω → c' ≤ ((αF (borelDiagFst b) : ℝˣ) : ℝ) / ((αF (borelDiagSnd b) : ℝˣ) : ℝ) →
        ‖Ec s ((b : AdelicGL2 (𝓞 F) F) * ω) -
            constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun t => unipotentGL2 t) (Ec s) ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤
          M * (((αF (borelDiagFst b) : ℝˣ) : ℝ) / ((αF (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N : ℝ))

theorem exists_bound_lambdaT {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (hdecay : DecayHyp hα O Ec)
    {α β : ℝ} (hαpos : 0 < α) (hαβ : α < β) (R : ℝ) {C : Set ℂ} (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ s ∈ C, ∀ x ∈ canonicalTruncationDomain F α β,
      ‖lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
        (adelicHeight F) (Real.exp R) (Ec s) x‖ ≤ G := by

  obtain ⟨hc0, hTc, hcover, hslab, hfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hαpos hαβ
  set c₀ := canonicalTruncationFloor F α β with hc₀def
  set u₀ := canonicalTruncationWindow F α β with hu₀def
  set d₁ := canonicalTruncationLowerCut F α β with hd₁def
  set d₂ := canonicalTruncationUpperCut F α β with hd₂def
  set Tc := canonicalTruncationTranslates F α β with hTcdef
  set Φ₀ := canonicalTruncationDomain F α β with hΦ₀def
  set c' : ℝ := c₀ ^ (∑ w : InfinitePlace F, w.mult) with hc'def
  have hc'pos : 0 < c' := pow_pos hc0 _
  have hSD : centreCutSiegelSet F c₀ u₀ d₁ d₂ ⊆ integralWindowedSiegelSet F c' u₀ :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc0.le

  set Ω : Set (AdelicGL2 (𝓞 F) F) := (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) ''
    ((adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ Tc) with hΩdef
  have hΩ : IsCompact Ω := ((isCompact_adelicMaximalCompact (K := F)).prod hTc).image continuous_mul

  obtain ⟨M, hM⟩ := hdecay C Ω c' 0 hC hCO hΩ hc'pos

  have hHc : Continuous (adelicHeight F) := NumberField.AdelicHeight.continuous_adelicHeight F
  have hinvc : ContinuousOn (fun z : AdelicGL2 (𝓞 F) F => (adelicHeight F z)⁻¹) Ω :=
    (hHc.continuousOn.inv₀ fun z _ => (adelicHeight_pos z).ne')
  obtain ⟨C₁, hC₁⟩ := hΩ.exists_bound_of_continuousOn hinvc
  set C₂ : ℝ := max C₁ 1 with hC₂def
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlow : ∀ z ∈ Ω, C₂⁻¹ ≤ adelicHeight F z := by
    intro z hz
    have h1 : (adelicHeight F z)⁻¹ ≤ C₂ := by
      have := hC₁ z hz
      rw [Real.norm_of_nonneg (inv_nonneg.2 (adelicHeight_pos z).le)] at this
      exact this.trans (le_max_left _ _)
    rw [inv_le_comm₀ hC₂pos (adelicHeight_pos z)]
    exact h1

  set T' : ℝ := Real.exp R * C₂ with hT'def
  obtain ⟨Kc, hKc, hcov⟩ := AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le F c' u₀ T' hc'pos
  obtain ⟨B, hB0, hB⟩ := D.exists_bound_on_compact_mul hC hCO hKc hTc
  refine ⟨max M B, le_trans hB0 (le_max_right _ _), fun s hs x hx => ?_⟩

  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  obtain ⟨g, hg, hgx⟩ := hxy
  have hgD := hSD hg
  have hxeq : x = g * y := hgx.symm
  obtain ⟨b, k, hgbk⟩ := exists_borel_mul_maximalCompact_eq F g
  have hky : (k : AdelicGL2 (𝓞 F) F) * y ∈ Ω := ⟨((k : AdelicGL2 (𝓞 F) F), y), ⟨k.2, hy⟩, rfl⟩
  have hxb : x = (b : AdelicGL2 (𝓞 F) F) * ((k : AdelicGL2 (𝓞 F) F) * y) := by rw [hxeq, hgbk, mul_assoc]
  have hHg : adelicHeight F g = hgt b := by rw [hgbk, adelicHeight_borel_mul_maximalCompact hα b k.2]
  have hgarch : adelicHeight F g = archHeight F (glArch (𝓞 F) F g) := adelicHeight_eq_archHeight_of_mem hgD.1
  have hc'g : c' ≤ hgt b := by rw [← hHg, hgarch]; exact hgD.2.1
  have hHx : adelicHeight F x = hgt b * adelicHeight F ((k : AdelicGL2 (𝓞 F) F) * y) := by
    rw [hxb, adelicHeight_borel_mul hα]
  by_cases hhigh : Real.exp R < adelicHeight F x
  ·
    rw [lambdaT_apply_of_lt _ _ hhigh]
    have h := hM s hs b ((k : AdelicGL2 (𝓞 F) F) * y) hky hc'g
    rw [← hxb] at h
    simp only [CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one] at h
    exact h.trans (le_max_left _ _)
  ·
    have hle : adelicHeight F x ≤ Real.exp R := not_lt.1 hhigh
    rw [lambdaT_apply_of_le _ _ hle]
    have hgT : archHeight F (glArch (𝓞 F) F g) ≤ T' := by
      rw [← hgarch, hHg]
      have h1 : hgt b * C₂⁻¹ ≤ Real.exp R := by
        calc hgt b * C₂⁻¹ ≤ hgt b * adelicHeight F ((k : AdelicGL2 (𝓞 F) F) * y) :=
              mul_le_mul_of_nonneg_left (hlow _ hky) (hgt_pos hα b).le
          _ = adelicHeight F x := hHx.symm
          _ ≤ Real.exp R := hle
      rw [hT'def]
      calc hgt b = hgt b * C₂⁻¹ * C₂ := by field_simp
        _ ≤ Real.exp R * C₂ := mul_le_mul_of_nonneg_right h1 hC₂pos.le
    obtain ⟨γ, z, hγ, hmem⟩ := hcov g hgD hgT
    have hγB : γ ∈ borelSubgroup F := hγ
    have e1 : ‖Ec s x‖ = ‖Ec s (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z * y)‖ := by
      rw [hxeq, ← D.apply_globalPoints_mul hγB (g * y) (hCO hs), ← D.norm_apply_mul_centralScalar z _ (hCO hs)]
      congr 2
      simp only [mul_assoc, mul_centralScalar_comm z y]
    rw [e1]
    exact (hB s hs _ hmem y hy).trans (le_max_right _ _)

end Bound

section Main

variable {F}

theorem memLp_two_lambdaT {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (hdecay : DecayHyp hα O Ec)
    {α β : ℝ} (hαpos : 0 < α) (hαβ : α < β) (R : ℝ) {s : ℂ} (hs : s ∈ O) :
    MemLp (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
        (adelicHeight F) (Real.exp R) (Ec s)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) := by
  obtain ⟨hc0, hTc, hcover, hslab, hfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hαpos hαβ
  obtain ⟨hnull, hfin⟩ := nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab hαpos hαβ hslab hfd
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨G, hG0, hG⟩ := exists_bound_lambdaT D hdecay hαpos hαβ R (isCompact_singleton (x := s))
    (Set.singleton_subset_iff.2 hs)
  refine MemLp.of_bound (measurable_lambdaT_of_continuous (D.continuous_apply hs) (Real.exp R)).aestronglyMeasurable
    G ?_
  rw [ae_restrict_iff'₀ hnull]
  exact Filter.Eventually.of_forall fun x hx => hG s rfl x hx

theorem tendsto_eLpNorm_lambdaT_sub {hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)} {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {O : Set ℂ} {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (D : FamilyData hα μ ν φ O Ec) (hdecay : DecayHyp hα O Ec)
    {α β : ℝ} (hαpos : 0 < α) (hαβ : α < β) (R : ℝ) {s₀ : ℂ} (hs₀ : s₀ ∈ O) :
    Filter.Tendsto (fun s : ℂ => eLpNorm (fun x : AdelicGL2 (𝓞 F) F =>
        lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
          (adelicHeight F) (Real.exp R) (Ec s) x -
        lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
          (adelicHeight F) (Real.exp R) (Ec s₀) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)))
      (nhdsWithin s₀ O) (nhds 0) := by
  obtain ⟨hc0, hTc, hcover, hslab, hfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hαpos hαβ
  obtain ⟨hnull, hfin⟩ := nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab hαpos hαβ hslab hfd
  set μΦ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β) with hμΦ
  haveI : IsFiniteMeasure μΦ := isFiniteMeasure_restrict.2 hfin.ne
  set Λ : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s x =>
    lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
      (adelicHeight F) (Real.exp R) (Ec s) x with hΛ

  obtain ⟨r, hr, hrO⟩ := (Metric.nhds_basis_closedBall.mem_iff).1 (D.hO.mem_nhds hs₀)
  have hCc : IsCompact (Metric.closedBall s₀ r) := isCompact_closedBall s₀ r
  obtain ⟨G, hG0, hG⟩ := exists_bound_lambdaT D hdecay hαpos hαβ R hCc hrO
  have hs₀C : s₀ ∈ Metric.closedBall s₀ r := Metric.mem_closedBall_self hr.le
  have hmemC : Metric.closedBall s₀ r ∈ 𝓝[O] s₀ :=
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds s₀ hr)

  set I : ℂ → ℝ≥0∞ := fun s => ∫⁻ x, ‖Λ s x - Λ s₀ x‖ₑ ^ (2 : ℝ) ∂μΦ with hI
  set K₀ : ℝ≥0∞ := (ENNReal.ofReal (G + G)) ^ (2 : ℝ) with hK₀
  have hK₀top : K₀ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hbound_pt : ∀ s ∈ Metric.closedBall s₀ r, ∀ x ∈ canonicalTruncationDomain F α β,
      ‖Λ s x - Λ s₀ x‖ₑ ^ (2 : ℝ) ≤ K₀ := by
    intro s hs x hx
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ‖Λ s x - Λ s₀ x‖ₑ ≤ ‖Λ s x‖ₑ + ‖Λ s₀ x‖ₑ := enorm_sub_le
      _ ≤ ENNReal.ofReal G + ENNReal.ofReal G := by
          refine add_le_add ?_ ?_
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hG s hs x hx)
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hG s₀ hs₀C x hx)
      _ = ENNReal.ofReal (G + G) := (ENNReal.ofReal_add hG0 hG0).symm
  have hIlim : Filter.Tendsto I (𝓝[O] s₀) (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μΦ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => K₀) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have h1 := measurable_lambdaT_of_continuous (D.continuous_apply hs) (Real.exp R)
      have h2 := measurable_lambdaT_of_continuous (D.continuous_apply hs₀) (Real.exp R)
      exact ((h1.sub h2).enorm).pow_const _
    · filter_upwards [hmemC] with s hs
      rw [ae_restrict_iff'₀ hnull]
      exact Filter.Eventually.of_forall fun x hx => hbound_pt s hs x hx
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top hK₀top (measure_ne_top _ _)
    · refine Filter.Eventually.of_forall fun x => ?_
      have hc : ContinuousWithinAt (fun s => Λ s x) O s₀ := continuousWithinAt_lambdaT D (Real.exp R) x hs₀
      have h2 : Filter.Tendsto (fun s => Λ s x - Λ s₀ x) (𝓝[O] s₀) (𝓝 0) := by
        have := hc.tendsto.sub_const (Λ s₀ x)
        rwa [sub_self] at this
      have h3 : Filter.Tendsto (fun s => ‖Λ s x - Λ s₀ x‖ₑ) (𝓝[O] s₀) (𝓝 0) := by
        have := h2.enorm
        rwa [enorm_zero] at this
      have h4 := h3.ennrpow_const (2 : ℝ)
      rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h4
  rw [lintegral_zero] at hIlim

  have heq : ∀ s, eLpNorm (fun x => Λ s x - Λ s₀ x) 2 μΦ = (I s) ^ (1 / (2 : ℝ)) := by
    intro s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp [hI]
  have hfin : Filter.Tendsto (fun s => (I s) ^ (1 / (2 : ℝ))) (𝓝[O] s₀) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    exact h.comp hIlim
  refine (Filter.tendsto_congr fun s => ?_).2 hfin
  exact heq s

end Main

end R1L2ContFamily
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family.R1L2ContFamily"

end
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family.R1L2ContFamily"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar in
open IsDedekindDomain in
open AutomorphicForm in
open scoped ComplexConjugate NNReal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hO : IsOpen O) (_hOc : IsPreconnected O) (_hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O)
      (_hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
      (_hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) O)
      (_hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ))
      (_hNjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (O ×ˢ Set.univ))
      (_hE : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = AutomorphicForm.pseudoEisenstein F (φ s) g)
      (_hN : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
      (_hdecay : ∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ O → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ ((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ) →
            ‖Ec s ((b : AdelicGL2 (𝓞 F) F) * ω) -
                AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                  (fun t => AutomorphicForm.unipotentGL2 t) (Ec s) ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤
              M * (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N : ℝ)))
      (R : ℝ),
    (∀ s ∈ O, MemLp (fun x : AdelicGL2 (𝓞 F) F => (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s)) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F α β))) ∧
    ∀ s₀ ∈ O, Filter.Tendsto
        (fun s : ℂ => eLpNorm (fun x : AdelicGL2 (𝓞 F) F => (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s)) x - (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s₀)) x) 2
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F α β)))
        (nhdsWithin s₀ O) (nhds 0) := by
  intro αm hαm μ ν hμ hν hμic hνic φ hφ _hφK _hφf hφjc _hφhol _hφKu O Ec Nc hO hOc hOhalf hEa _hNa hEjc _hNjc
    hE _hN hdecay R
  have D : R1L2ContFamily.FamilyData hαm μ ν φ O Ec :=
    { hμ := hμ, hν := hν, hμic := hμic, hνic := hνic, hφ := hφ, hφjc := hφjc, hO := hO, hOc := hOc,
      hOhalf := hOhalf, hEa := hEa, hEjc := hEjc, hE := hE }
  exact ⟨fun s hs => R1L2ContFamily.memLp_two_lambdaT D hdecay hα hαβ R hs,
    fun s₀ hs₀ => R1L2ContFamily.tendsto_eLpNorm_lambdaT_sub D hdecay hα hαβ R hs₀⟩

end S_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
end P2MW
export P2MW.S_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family (solution)
