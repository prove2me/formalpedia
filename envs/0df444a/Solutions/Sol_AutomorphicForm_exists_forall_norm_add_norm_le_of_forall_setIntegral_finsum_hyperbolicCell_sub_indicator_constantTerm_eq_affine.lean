-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/45f120f4-1c0c-52e9-9733-337802090a44

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_sum_integral_norm_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply"
p2m_attr_erase "simp" "Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply"
p2m_attr_erase "simp" "Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4BGlue

section TwistCentral

variable {G : Type*} [Group G]

def twistCentralSubgroup (f : G →* G) : Subgroup G where
  carrier := {h | f h * h⁻¹ ∈ Subgroup.center G}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, inv_one, mul_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hc := Subgroup.mem_center_iff.mp hb
    have : f (a * b) * (a * b)⁻¹ = (f a * a⁻¹) * (a * (f b * b⁻¹) * a⁻¹) := by
      simp only [map_mul, mul_inv_rev]; group
    rw [this, hc a, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hc := Subgroup.mem_center_iff.mp ha
    have : f a⁻¹ * a⁻¹⁻¹ = (a⁻¹ * (f a * a⁻¹) * a)⁻¹ := by
      simp only [map_inv]; group
    rw [this, hc a⁻¹, inv_mul_cancel_right]
    exact Subgroup.inv_mem _ ha

theorem mem_twistCentralSubgroup (f : G →* G) (h : G) :
    h ∈ twistCentralSubgroup f ↔ f h * h⁻¹ ∈ Subgroup.center G := Iff.rfl

end TwistCentral

section Diag

variable (A : Type*) [CommRing A]

def diagSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {h | (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ha1, ha2]

variable {A}

theorem mem_diagSubgroup (h : GL (Fin 2) A) :
    h ∈ diagSubgroup A ↔
      (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := Iff.rfl

theorem mul_comm_of_mem_diagSubgroup {a b : GL (Fin 2) A} (ha : a ∈ diagSubgroup A)
    (hb : b ∈ diagSubgroup A) : a * b = b * a := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine Units.ext ?_
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [ha1, ha2, hb1, hb2, mul_comm]

end Diag

section H

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def theH : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  diagSubgroup (AdeleRing (𝓞 L) L) ⊓ twistCentralSubgroup (AutomorphicForm.sigmaAdelicAct K L D σ)

theorem mem_theH (h : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    h ∈ theH K L D σ ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
         Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  rw [theH, Subgroup.mem_inf, mem_diagSubgroup, mem_twistCentralSubgroup, and_assoc]

theorem isClosed_theH :
    IsClosed ((theH K L D σ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
      Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  have h1 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0} :=
    isClosed_eq (Units.continuous_val.matrix_elem 1 0) continuous_const
  have h2 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0} :=
    isClosed_eq (Units.continuous_val.matrix_elem 0 1) continuous_const
  have hZ : IsClosed ((Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
    have : ((Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
        ⋂ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, {z | g * z = z * g} := by
      ext z
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g =>
      isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have h3 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
        Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)} :=
    hZ.preimage ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).mul continuous_inv)
  have hEq : ((theH K L D σ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
      Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
      ({h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
          (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0} ∩
        {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
          (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0}) ∩
      {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
        AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
          Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)} := by
    ext h
    simp only [SetLike.mem_coe, mem_theH, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [hEq]
  exact (h1.inter h2).inter h3

theorem theH_mul_comm (a b : theH K L D σ) : a * b = b * a := by
  refine Subtype.ext ?_
  show (a : AutomorphicForm.AdelicGL2 (𝓞 L) L) * b = b * a
  exact mul_comm_of_mem_diagSubgroup (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1

theorem exists_haar_theH :
    ∃ μH : Measure (theH K L D σ), μH.IsHaarMeasure ∧ μH.IsMulRightInvariant := by
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : LocallyCompactSpace (theH K L D σ) := (isClosed_theH K L D σ).locallyCompactSpace
  refine ⟨Measure.haar, inferInstance, ⟨fun g => ?_⟩⟩
  have : (fun x : theH K L D σ => x * g) = fun x => g * x := funext fun x => theH_mul_comm K L D σ x g
  rw [this]
  exact map_mul_left_eq_self _ g

end H

section Delta

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include hgen in

theorem exists_Delta : ∃ Δ : Set (GL (Fin 2) L),
    (∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) ∧
    (∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    ({δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) := by
  classical
  obtain ⟨-, h2, h3⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := L) hgen

  let cls : GL (Fin 2) L → Set (GL (Fin 2) L) := fun t => {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
    t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
  let good : GL (Fin 2) L → Prop := fun t =>
    ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1

  let S : Set (Set (GL (Fin 2) L)) := {s | ∃ t, good t ∧ cls t = s}
  have hS : ∀ s : S, ∃ t, good t ∧ cls t = s := fun s => s.2
  choose pick hpick using hS
  refine ⟨Set.range pick, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(hpick s).1.1.1, (hpick s).1.1.2, (hpick s).1.2⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne
    have hss : (s : Set (GL (Fin 2) L)) ≠ s' := fun h => hne (by rw [Subtype.ext h])
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne'
    have h := ((h3 (pick s') (pick s) (hpick s').1.1 (hpick s).1.1).1).mp hne'
    exact hss (by rw [← (hpick s).2, ← (hpick s').2]; exact h)
  · intro δ hδ
    obtain ⟨t, htd, htN, ht⟩ := h2 δ hδ
    have hs : cls t ∈ S := ⟨t, ⟨htd, htN⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨pick ⟨_, hs⟩, ⟨⟨_, hs⟩, rfl⟩, ?_⟩
    have hct : cls (pick ⟨cls t, hs⟩) = cls t := (hpick ⟨_, hs⟩).2
    show δ ∈ cls (pick ⟨cls t, hs⟩)
    rw [hct]
    exact ht

end Delta

section Fact

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open scoped TensorProduct.RightActions in

theorem eq_of_isSemiLocalFactorization (S : Finset (HeightOneSpectrum (𝓞 K)))
    {φ₁ φ₂ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf₁ φf₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h₁ : AutomorphicForm.IsSemiLocalFactorization K L S φ₁ φa φf₁ φS)
    (h₂ : AutomorphicForm.IsSemiLocalFactorization K L S φ₂ φa φf₂ φS) : φ₁ = φ₂ := by
  obtain ⟨-, -, -, hint₁, hout₁, hφ₁⟩ := h₁
  obtain ⟨-, -, -, hint₂, hout₂, hφ₂⟩ := h₂
  have hf : φf₁ = φf₂ := by
    funext h
    by_cases hh : ∀ v ∉ S,
        AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v
    · rw [hint₁ h hh, hint₂ h hh]
    · push Not at hh
      rw [hout₁ h hh, hout₂ h hh]
  funext g
  rw [hφ₁ g, hφ₂ g, hf]

open scoped TensorProduct.RightActions in

theorem continuous_and_hasCompactSupport_of_isSemiLocalFactorization
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    Continuous φ ∧ HasCompactSupport φ :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    ⟨φa, φf, h.1, h.2.1, h.2.2.2.2.2⟩

end Fact

section Affine

theorem eq_and_eq_of_forall_le {ν₀ μ₀ ν₁ μ₁ : ℂ} (R₂ : ℝ)
    (h : ∀ R : ℝ, R₂ ≤ R → (R : ℂ) * ν₀ + μ₀ = (R : ℂ) * ν₁ + μ₁) : ν₀ = ν₁ ∧ μ₀ = μ₁ := by
  have h0 := h R₂ le_rfl
  have h1 := h (R₂ + 1) (by linarith)
  have hν : ν₀ = ν₁ := by
    have e : ((R₂ + 1 : ℝ) : ℂ) * ν₀ + μ₀ - ((R₂ : ℂ) * ν₀ + μ₀) =
        ((R₂ + 1 : ℝ) : ℂ) * ν₁ + μ₁ - ((R₂ : ℂ) * ν₁ + μ₁) := by rw [h1, h0]
    push_cast at e
    linear_combination e
  refine ⟨hν, ?_⟩
  rw [hν] at h0
  linear_combination h0

theorem norm_sum_add_norm_sum_le {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Finset ι}
    {a : ι → ℂ} {Ca : ℝ} (hCa : ∀ t, ‖a t‖ ≤ Ca) {F : ι → X → ℂ} {w : X → ℂ} {CB : ℝ}
    (hB : ∑ t ∈ s, ((∫ x, ‖F t x‖ ∂μ) + ∫ x, ‖w x * F t x‖ ∂μ) ≤ CB) :
    ‖∑ t ∈ s, a t * ∫ x, w x * F t x ∂μ‖ + ‖∑ t ∈ s, 2 * a t * ∫ x, F t x ∂μ‖ ≤
      2 * max Ca 0 * CB := by
  have hCa' : ∀ t, ‖a t‖ ≤ max Ca 0 := fun t => (hCa t).trans (le_max_left _ _)
  have hM : 0 ≤ max Ca 0 := le_max_right _ _
  have h1 : ‖∑ t ∈ s, a t * ∫ x, w x * F t x ∂μ‖ ≤ ∑ t ∈ s, max Ca 0 * ∫ x, ‖w x * F t x‖ ∂μ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hCa' t) (norm_integral_le_integral_norm _) (norm_nonneg _) hM
  have h2 : ‖∑ t ∈ s, 2 * a t * ∫ x, F t x ∂μ‖ ≤ ∑ t ∈ s, 2 * max Ca 0 * ∫ x, ‖F t x‖ ∂μ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hCa' t) (by norm_num))
      (norm_integral_le_integral_norm _) (norm_nonneg _) (by positivity)
  calc ‖∑ t ∈ s, a t * ∫ x, w x * F t x ∂μ‖ + ‖∑ t ∈ s, 2 * a t * ∫ x, F t x ∂μ‖
      ≤ (∑ t ∈ s, max Ca 0 * ∫ x, ‖w x * F t x‖ ∂μ) + ∑ t ∈ s, 2 * max Ca 0 * ∫ x, ‖F t x‖ ∂μ :=
        add_le_add h1 h2
    _ ≤ (∑ t ∈ s, 2 * max Ca 0 * ∫ x, ‖w x * F t x‖ ∂μ) + ∑ t ∈ s, 2 * max Ca 0 * ∫ x, ‖F t x‖ ∂μ := by
        gcongr with t _
        linarith [hM]
    _ = 2 * max Ca 0 * ∑ t ∈ s, ((∫ x, ‖F t x‖ ∂μ) + ∫ x, ‖w x * F t x‖ ∂μ) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun t _ => add_comm _ _
    _ ≤ 2 * max Ca 0 * CB := mul_le_mul_of_nonneg_left hB (by positivity)

end Affine

end R4BGlue

end

open AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
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
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∀ (μ₀ ν₀ : ℂ) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (R : ℂ) * ν₀ + μ₀) →
        ‖μ₀‖ + ‖ν₀‖ ≤ C * ∏ v ∈ T,
          ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖) ^ ks v *
            ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ^ js v) := by
  intro T hT hTS ws w' hw' ϖs hϖ hϖs0 ns rTs hrTs zs hzs

  obtain ⟨μH, hμH, hμHr⟩ := R4BGlue.exists_haar_theH K L D σ

  obtain ⟨Δ, hΔd, hΔdisj, hΔcov⟩ := R4BGlue.exists_Delta (K := K) (L := L) (σ := σ) hgen

  have hE :=
    AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
      K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
      (R4BGlue.theH K L D σ) (R4BGlue.isClosed_theH K L D σ) (R4BGlue.mem_theH K L D σ) μH Δ hΔd hΔdisj hΔcov

  obtain ⟨CB, hCB, hO⟩ :=
    AutomorphicForm.exists_forall_sum_integral_norm_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization
      K L νZL D σ hgen SL ξL hξc hξt S φa φS
      (R4BGlue.theH K L D σ) (R4BGlue.isClosed_theH K L D σ) (R4BGlue.mem_theH K L D σ) μH Δ hΔd hΔdisj
      T hT hTS ws w' hw' ϖs hϖ hϖs0 ns rTs hrTs zs hzs
  by_cases hinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩
  ·
    obtain ⟨a, ⟨Ca, hCa⟩, hA⟩ := hE.1 hinv
    refine ⟨2 * max Ca 0 * CB, by positivity, ?_⟩
    intro ks js φ φf hfact μ₀ ν₀ R₀ haff
    obtain ⟨Δφ, hΔφ, -, -, R₁, hR₁⟩ := hA φ ⟨φa, φf, hfact.1, hfact.2.1, hfact.2.2.2.2.2⟩
    obtain ⟨hν, hμ⟩ := R4BGlue.eq_and_eq_of_forall_le (ν₀ := ν₀) (μ₀ := μ₀) (max R₀ R₁)
      (fun R hR => (haff R ((le_max_left _ _).trans hR)).symm.trans
        (hR₁ R ((le_max_right _ _).trans hR)).2.2)
    rw [hν, hμ]
    calc _ ≤ 2 * max Ca 0 * (CB * _) :=
          R4BGlue.norm_sum_add_norm_sum_le hCa (hO ks js φ φf hfact Δφ hΔφ)
      _ = 2 * max Ca 0 * CB * _ := (mul_assoc _ _ _).symm
  ·
    refine ⟨0, le_rfl, ?_⟩
    intro ks js φ φf hfact μ₀ ν₀ R₀ haff
    obtain ⟨R₁, hR₁⟩ := hE.2 hinv φ ⟨φa, φf, hfact.1, hfact.2.1, hfact.2.2.2.2.2⟩
    obtain ⟨hν, hμ⟩ := R4BGlue.eq_and_eq_of_forall_le (ν₀ := ν₀) (μ₀ := μ₀) (ν₁ := 0) (μ₁ := 0) (max R₀ R₁)
      (fun R hR => (haff R ((le_max_left _ _).trans hR)).symm.trans
        ((hR₁ R ((le_max_right _ _).trans hR)).2.2.trans (show (0 : ℂ) = (R : ℂ) * 0 + 0 by ring)))
    rw [hν, hμ, norm_zero, add_zero, zero_mul]

end S_AutomorphicForm_exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine (solution)
