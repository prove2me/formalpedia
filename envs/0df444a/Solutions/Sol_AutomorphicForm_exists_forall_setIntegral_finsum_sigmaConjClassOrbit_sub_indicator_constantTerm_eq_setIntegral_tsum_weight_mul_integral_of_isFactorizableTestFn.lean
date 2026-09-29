-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0f20fb4a-ccef-530a-820c-025b2a7b41df

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
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives
import Theorems.Thm_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
import Theorems.Thm_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply"
p2m_attr_erase "simp" "Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace U0R
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def Adiag (L : Type) [Field L] : Subgroup (GL (Fin 2) L) where
  carrier := {a | (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    constructor
    · rw [ha.1, hb.1]; ring
    · rw [ha.2, hb.2]; ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have hdet : (a : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, ha.1, mul_zero, sub_zero] at hdet
    obtain ⟨h00, h11⟩ := mul_ne_zero_iff.mp hdet
    have hmul : (a : Matrix (Fin 2) (Fin 2) L) * ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e10 := congrFun (congrFun hmul 1) 0
    have e01 := congrFun (congrFun hmul 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ha.1, ha.2, zero_mul, add_zero, zero_add] at e10 e01
    simp only [Fin.isValue, Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero, if_false] at e10 e01
    exact ⟨(mul_eq_zero.mp e10).elim (fun h => absurd h h11) id, (mul_eq_zero.mp e01).elim (fun h => absurd h h00) id⟩

def LamP : Subgroup (GL (Fin 2) L) where
  carrier := {a | ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
    (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)}
  one_mem' := by refine ⟨by simp, 1, by simp⟩
  mul_mem' := by
    intro a b ha hb
    have hab := (Adiag L).mul_mem ha.1 hb.1
    refine ⟨hab, ?_⟩
    obtain ⟨ka, hka⟩ := ha.2; obtain ⟨kb, hkb⟩ := hb.2
    refine ⟨ka * kb, ?_⟩
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1.1, ha.1.2, hb.1.1, hb.1.2, mul_zero, zero_mul,
      add_zero, zero_add, map_mul, hka, hkb]
    have hdetb : (b : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, hb.1.1, mul_zero, sub_zero] at hdetb
    have hdeta : (a : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, ha.1.1, mul_zero, sub_zero] at hdeta
    obtain ⟨-, ha11⟩ := mul_ne_zero_iff.mp hdeta; obtain ⟨-, hb11⟩ := mul_ne_zero_iff.mp hdetb
    field_simp
  inv_mem' := by
    intro a ha
    have hai := (Adiag L).inv_mem ha.1
    refine ⟨hai, ?_⟩
    obtain ⟨ka, hka⟩ := ha.2
    have hdeta : (a : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, ha.1.1, mul_zero, sub_zero] at hdeta
    obtain ⟨ha00, ha11⟩ := mul_ne_zero_iff.mp hdeta
    have hka0 : ka ≠ 0 := by
      intro h0; rw [h0, map_zero, eq_comm, div_eq_zero_iff] at hka; exact hka.elim ha00 ha11
    refine ⟨ka⁻¹, ?_⟩
    have hmul : (a : Matrix (Fin 2) (Fin 2) L) * ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e00 := congrFun (congrFun hmul 0) 0
    have e11 := congrFun (congrFun hmul 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ha.1.1, ha.1.2, zero_mul, add_zero, zero_add,
      if_true] at e00 e11
    have hi00 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ := by
      field_simp at e00 ⊢; linear_combination e00
    have hi11 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = ((a : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ := by
      field_simp at e11 ⊢; linear_combination e11
    rw [hi00, hi11, map_inv₀, hka]
    field_simp

abbrev Kap : Type := Adiag L ⧸ (LamP K L).subgroupOf (Adiag L)

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  have hinj : Function.Injective
      (Units.val : (Matrix (Fin 2) (Fin 2) L)ˣ → Matrix (Fin 2) (Fin 2) L) := fun _ _ h => Units.ext h
  exact hinj.countable

scoped instance countable_Kap : Countable (Kap K L) := by
  haveI := countable_GL2 (L := L)
  haveI : Countable (Adiag L) := Subtype.countable
  exact Quotient.countable

noncomputable def ra (j : Kap K L) : GL (Fin 2) L := ((Quotient.out j : Adiag L) : GL (Fin 2) L)

theorem hrad (j : Kap K L) : ((ra K L j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra K L j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0 :=
  (Quotient.out j : Adiag L).2

theorem hra (a : GL (Fin 2) L) (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ∃! j : Kap K L, (ra K L j)⁻¹ * a ∈ LamP K L := by
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : Adiag L) : Kap K L), ?_, ?_⟩
  · have h := QuotientGroup.out_eq' (QuotientGroup.mk (s := (LamP K L).subgroupOf (Adiag L)) (⟨a, ha⟩ : Adiag L))
    have := QuotientGroup.eq.mp h
    simpa [ra, Subgroup.mem_subgroupOf] using this
  · intro j hj
    have : QuotientGroup.mk (s := (LamP K L).subgroupOf (Adiag L)) (Quotient.out j) =
        QuotientGroup.mk (s := (LamP K L).subgroupOf (Adiag L)) (⟨a, ha⟩ : Adiag L) := by
      apply QuotientGroup.eq.mpr
      simpa [ra, Subgroup.mem_subgroupOf] using hj
    rw [← this]; exact (QuotientGroup.out_eq' j).symm

end U0R
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn.U0R"

open scoped TensorProduct.RightActions in
open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)

    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in Φ₀, ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)  := by
  classical
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφ
  have hΛ' : ∀ a : GL (Fin 2) L, a ∈ U0R.LamP K L ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L) :=
    fun a => Iff.rfl

  obtain ⟨R₀, hC3c⟩ :=
    AutomorphicForm.exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn
      K L νZL ΩL hΩL D σ hgen ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr α β hα hαβ c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
      (U0R.LamP K L) hΛ' (U0R.ra K L) (U0R.hrad K L) (U0R.hra K L) φ hφ
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hDint, hD0⟩ := hC3c R hR
  obtain ⟨-, hRint⟩ := AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
    δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr φ hφc hφs R

  have hpt : ∀ x : AdelicGL2 (𝓞 L) L, (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x = (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) x + (fun x : AdelicGL2 (𝓞 L) L =>
        (∑' i,
          (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) x := by
    intro x
    obtain ⟨-, hfin1, hfin⟩ :=
      AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
        K L νZL ΩL hΩL D σ ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr φ hφc hφs x
    obtain ⟨hKint, hFsum, hKeq⟩ :=
      (AutomorphicForm.integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives
        K L νZL ΩL hΩL D σ ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr φ hφc hφs x).2 hfin
    obtain ⟨-, hCTint, hGsum, hCTeq⟩ :=
      AutomorphicForm.setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
        K L νZL ΩL hΩL D σ hgen ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr ΦL (U0R.LamP K L) hΛ' (U0R.ra K L)
        (U0R.hrad K L) (U0R.hra K L) φ hφc hφs x R

    have hFabs : Summable (fun i => ‖∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖) := by
      have hs : Summable (fun i => (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL).toReal) :=
        ENNReal.summable_toReal hfin.ne
      refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hs
      refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
      congr 1
      refine lintegral_congr (fun z => ?_)
      rw [ofReal_norm_eq_enorm]
    have hbd1 : ∀ i, ‖(Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) * ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ ≤ 2 * ‖∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ := by
      intro i
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Set.indicator_apply]
      split_ifs <;> norm_num
    have hbd2 : ∀ i, ‖(1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) * ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ ≤ 3 * ‖∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ := by
      intro i
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Set.indicator_apply]
      split_ifs <;> norm_num
    have hS1 : Summable (fun i => (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) * ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) :=
      Summable.of_norm_bounded (hFabs.mul_left 2) hbd1
    have hS2 : Summable (fun i => (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) * ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) :=
      Summable.of_norm_bounded (hFabs.mul_left 3) hbd2

    have e1 : (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x = (∑' i, ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) := by
      simp only []
      rw [← hKeq, ← hCTeq, ← integral_sub hKint hCTint]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      ring

    have e2 : (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) x + (fun x : AdelicGL2 (𝓞 L) L =>
        (∑' i,
          (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) x = (∑' i, ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) := by
      simp only []
      rw [add_sub, ← hS2.tsum_add hS1]
      congr 1
      refine tsum_congr (fun i => ?_)
      ring
    exact e1.trans e2.symm
  have hfun : (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) = fun x => (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) x + (fun x : AdelicGL2 (𝓞 L) L =>
        (∑' i,
          (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (U0R.ra K L j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) x := funext hpt
  refine ⟨?_, hRint, ?_⟩
  · rw [hfun]; exact hRint.add hDint
  · rw [hfun, integral_add hRint hDint, hD0, add_zero]

end S_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn (solution)
