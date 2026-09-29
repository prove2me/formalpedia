-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0f70fccb-5e5f-54b3-8e8c-c6eb4f3ab283

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
import Theorems.Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
import Theorems.Thm_AutomorphicForm_lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj"
p2m_attr_erase "simp" "JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace TranslatesGlue

p2m_open "AutomorphicForm~continuous_semiLocalEval~continuous_glMap~continuous_semiLocalComponent"
open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_semiLocalEval (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (AutomorphicForm.semiLocalEval K L v) := by
  have h1 : Continuous (AutomorphicForm.semiLocalHomeomorph K L v).symm :=
    (AutomorphicForm.semiLocalHomeomorph K L v).symm.continuous
  have h2 : Continuous (RingHom.pi fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1) :=
    continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1
  exact h1.comp h2

theorem continuous_semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (AutomorphicForm.semiLocalComponent K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact continuous_glMap _ (continuous_semiLocalEval K L v)

theorem isLocallyConstant_finset_prod {X α : Type*} [TopologicalSpace X] (s : Finset α) (f : α → X → ℂ)
    (h : ∀ a ∈ s, IsLocallyConstant (f a)) : IsLocallyConstant fun x => ∏ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const _
  | insert a s ha ih =>
    have e : (fun x => ∏ b ∈ insert a s, f b x) = f a * fun x => ∏ b ∈ s, f b x := by
      funext x; rw [Finset.prod_insert ha]; rfl
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem isLocallyConstant_finset_sum {X α : Type*} [TopologicalSpace X] (s : Finset α) (f : α → X → ℂ)
    (h : ∀ a ∈ s, IsLocallyConstant (f a)) : IsLocallyConstant fun x => ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const _
  | insert a s ha ih =>
    have e : (fun x => ∑ b ∈ insert a s, f b x) = f a + fun x => ∑ b ∈ s, f b x := by
      funext x; rw [Finset.sum_insert ha]; rfl
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

section Weights

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

def P (a : ∀ i, κ i → ℂ) (p : ∀ i, κ i) : ℂ := ∏ i, a i (p i)

def Q (a : ∀ i, κ i → ℂ) : ℂ := ∏ i, ∑ k, a i k

theorem sum_P [DecidableEq ι] (a : ∀ i, κ i → ℂ) : ∑ p, P a p = Q a := by
  unfold P Q
  exact (Fintype.prod_sum a).symm

theorem P_eq_zero_of_Q_eq_zero (a : ∀ i, κ i → ℂ) (ha : ∀ i k, a i k = 0 ∨ a i k = 1) (hQ : Q a = 0)
    (p : ∀ i, κ i) : P a p = 0 := by
  classical
  unfold Q at hQ
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hQ
  unfold P
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hcount : (∑ k, a i k) = ((Finset.univ.filter fun k => a i k = 1).card : ℂ) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases ha i k with h | h <;> simp [h]
  rw [hcount, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hi
  rcases ha i (p i) with h | h
  · exact h
  · exact absurd h (hi (Finset.mem_univ _))

theorem mul_Q_mul_P_div_Q (a : ∀ i, κ i → ℂ) (ha : ∀ i k, a i k = 0 ∨ a i k = 1) (R : ℂ) (p : ∀ i, κ i) :
    R * Q a * (P a p / Q a) = R * P a p := by
  by_cases hQ : Q a = 0
  · rw [P_eq_zero_of_Q_eq_zero a ha hQ p, hQ]; simp
  · rw [mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hQ]

theorem sum_mul_P_div_Q [DecidableEq ι] (a : ∀ i, κ i → ℂ) (x : ℂ) (hx : Q a = 0 → x = 0) :
    ∑ p, x * (P a p / Q a) = x := by
  rw [← Finset.mul_sum, ← Finset.sum_div, sum_P]
  by_cases hQ : Q a = 0
  · rw [hx hQ]; simp
  · rw [div_self hQ, mul_one]

end Weights

section Translates

variable (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))

def wt (v : HeightOneSpectrum (𝓞 K)) (r : GL (Fin 2) ((ws v).1.adicCompletion L))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : ℂ :=
  (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
    ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 r))⁻¹ *
      AutomorphicForm.semiLocalComponent K L v h)

theorem wt_eq_zero_or_one (v : HeightOneSpectrum (𝓞 K)) (r : GL (Fin 2) ((ws v).1.adicCompletion L))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : wt K L ws v r h = 0 ∨ wt K L ws v r h = 1 := by
  unfold wt
  by_cases hm : (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 r))⁻¹ *
      AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v
  · rw [Set.indicator_of_mem hm]; exact Or.inr rfl
  · rw [Set.indicator_of_notMem hm]; exact Or.inl rfl

theorem isLocallyConstant_wt (v : HeightOneSpectrum (𝓞 K)) (r : GL (Fin 2) ((ws v).1.adicCompletion L)) :
    IsLocallyConstant (wt K L ws v r) := by
  haveI hG := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hG.toContinuousMul
  unfold wt
  exact (AutomorphicForm.isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v).1.comp_continuous
    ((continuous_const.mul (continuous_semiLocalComponent K L v)))

theorem isSemiLocalTestFn_indicator_translate (v : HeightOneSpectrum (𝓞 K))
    (r : GL (Fin 2) ((ws v).1.adicCompletion L)) :
    AutomorphicForm.IsSemiLocalTestFn K L v (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
        ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 r))⁻¹ * x)) := by
  haveI hG := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hG.toContinuousMul
  obtain ⟨hlc, hcs⟩ := AutomorphicForm.isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
  refine ⟨hlc.comp_continuous (continuous_const.mul continuous_id), ?_⟩
  exact hcs.comp_homeomorph (Homeomorph.mulLeft
    ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 r))⁻¹))

variable [DecidableEq (HeightOneSpectrum (𝓞 K))] (T : Finset (HeightOneSpectrum (𝓞 K))) (N : HeightOneSpectrum (𝓞 K) → ℕ)
  (ρ : ∀ v : HeightOneSpectrum (𝓞 K), Fin (N v) → GL (Fin 2) ((ws v).1.adicCompletion L))

def wts (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : ∀ v : ↥T, Fin (N v) → ℂ :=
  fun v k => wt K L ws v (ρ v k) h

def rhoSel (p : ∀ v : ↥T, Fin (N v)) : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L) :=
  fun v => if hv : v ∈ T then ρ v (p ⟨v, hv⟩) else 1

theorem rhoSel_coe (p : ∀ v : ↥T, Fin (N v)) (v : ↥T) : rhoSel K L ws T N ρ p v = ρ v (p v) := by
  unfold rhoSel
  rw [dif_pos v.2]

variable (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)

def phifSel (p : ∀ v : ↥T, Fin (N v))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : ℂ :=
  φf h * (P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h))

def phiSel (p : ∀ v : ↥T, Fin (N v))
    (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  φa (AdelicLevel.glArch (𝓞 L) L g) * phifSel K L ws T N ρ φf p (AdelicLevel.glFin (𝓞 L) L g)

end Translates

theorem prod_union_ite {α β : Type*} [CommMonoid β] [DecidableEq α] (S T : Finset α) (X Y : α → β) :
    ∏ v ∈ S ∪ T, (if v ∈ T then X v else Y v) = (∏ v ∈ S \ T, Y v) * ∏ v ∈ T, X v := by
  rw [← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.mp hv).2
  · exact Finset.prod_congr rfl fun v hv => if_pos hv

section Factorization

variable [DecidableEq (HeightOneSpectrum (𝓞 K))]
  (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
  (S T : Finset (HeightOneSpectrum (𝓞 K))) (N : HeightOneSpectrum (𝓞 K) → ℕ)
  (ρ : ∀ v : HeightOneSpectrum (𝓞 K), Fin (N v) → GL (Fin 2) ((ws v).1.adicCompletion L))
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

theorem prod_family_eq (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (∏ v ∈ S ∪ T, (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ i : Fin (N v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v i)))⁻¹ * x)
            else φS v) v (semiLocalComponent K L v h)) =
      (∏ v ∈ S \ T, φS v (semiLocalComponent K L v h)) * Q (wts K L ws T N ρ h) := by
  simp only [ite_apply]
  rw [prod_union_ite]
  congr 1
  unfold Q wts wt
  exact (Finset.prod_coe_sort T _).symm

theorem prod_single_eq (p : ∀ v : ↥T, Fin (N v)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (∏ v ∈ S ∪ T, (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (rhoSel K L ws T N ρ p v)))⁻¹ * x)
            else φS v) v (semiLocalComponent K L v h)) =
      (∏ v ∈ S \ T, φS v (semiLocalComponent K L v h)) * P (wts K L ws T N ρ h) p := by
  simp only [ite_apply]
  rw [prod_union_ite]
  congr 1
  unfold P wts wt
  rw [← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [rhoSel_coe]

variable (φ : AdelicGL2 (𝓞 L) L → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
  (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)

omit [DecidableEq (HeightOneSpectrum (𝓞 K))] in
theorem isLocallyConstant_theta (p : ∀ v : ↥T, Fin (N v)) :
    IsLocallyConstant fun h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) =>
      P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h) := by
  have hP : IsLocallyConstant fun h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) => P (wts K L ws T N ρ h) p := by
    unfold P wts
    exact isLocallyConstant_finset_prod (Finset.univ : Finset ↥T) (fun (v : ↥T) h => wt K L ws v (ρ v (p v)) h)
      fun v _ => isLocallyConstant_wt K L ws v _
  have hQ : IsLocallyConstant fun h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) => Q (wts K L ws T N ρ h) := by
    unfold Q wts
    exact isLocallyConstant_finset_prod (Finset.univ : Finset ↥T) (fun (v : ↥T) h => ∑ k, wt K L ws v (ρ v k) h)
      fun v _ => isLocallyConstant_finset_sum (Finset.univ : Finset (Fin (N v)))
        (fun k h => wt K L ws v (ρ v k) h) fun k _ => isLocallyConstant_wt K L ws v _
  exact hP.div hQ

theorem isSemiLocalFactorization_sel
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ i : Fin (N v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v i)))⁻¹ * x)
            else φS v))
    (p : ∀ v : ↥T, Fin (N v)) :
    IsSemiLocalFactorization K L (S ∪ T) (phiSel K L ws T N ρ φf φa p) φa (phifSel K L ws T N ρ φf p)
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (rhoSel K L ws T N ρ p v)))⁻¹ * x)
            else φS v) := by
  obtain ⟨hφa, hφf, hΨ, h4, h5, h6⟩ := hfact
  refine ⟨hφa, ⟨?_, ?_⟩, ?_, ?_, ?_, fun g => rfl⟩
  · show IsLocallyConstant (φf * fun h => P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h))
    exact hφf.1.mul (isLocallyConstant_theta K L ws T N ρ p)
  · show HasCompactSupport (φf * fun h => P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h))
    exact hφf.2.mul_right
  · intro v hv
    by_cases hvT : v ∈ T
    · show IsSemiLocalTestFn K L v (if v ∈ T then _ else _)
      rw [if_pos hvT]
      exact isSemiLocalTestFn_indicator_translate K L ws v (rhoSel K L ws T N ρ p v)
    · have := hΨ v hv
      show IsSemiLocalTestFn K L v (if v ∈ T then _ else _)
      rw [if_neg hvT]
      have e : (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ i : Fin (N v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v i)))⁻¹ * x)
            else φS v) v = φS v := if_neg hvT
      rwa [e] at this
  · intro h hint
    have e0 := h4 h hint
    rw [prod_family_eq] at e0
    show φf h * (P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h)) = _
    rw [prod_single_eq, e0]
    exact mul_Q_mul_P_div_Q _ (fun (v : ↥T) k => wt_eq_zero_or_one K L ws v (ρ v k) h) _ _
  · intro h hnot
    show φf h * (P (wts K L ws T N ρ h) p / Q (wts K L ws T N ρ h)) = 0
    rw [h5 h hnot, zero_mul]

theorem eq_sum_phiSel
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ i : Fin (N v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v i)))⁻¹ * x)
            else φS v))
    (x : AdelicGL2 (𝓞 L) L) : φ x = ∑ p : (∀ v : ↥T, Fin (N v)), phiSel K L ws T N ρ φf φa p x := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := hfact
  rw [h6 x]
  simp only [phiSel, phifSel]
  rw [← Finset.mul_sum]
  congr 1
  symm
  apply sum_mul_P_div_Q
  intro hQ
  by_cases hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L x) ∈ semiLocalIntegralSet K L v
  · rw [h4 _ hint, prod_family_eq, hQ, mul_zero]
  · push Not at hint
    exact h5 _ hint

end Factorization

section Assembly

open scoped ENNReal

theorem sum_add_le_of_split {ι J : Type*} [Fintype J] (s : Finset ι) (A B : ι → ℝ≥0∞) (A' B' : ι → J → ℝ≥0∞)
    (C X : ℝ≥0∞) (hA : ∀ t ∈ s, A t ≤ ∑ j, A' t j) (hB : ∀ t ∈ s, B t ≤ ∑ j, B' t j)
    (hS : ∀ j, ∑ t ∈ s, (A' t j + B' t j) ≤ C) (hX : (Fintype.card J : ℝ≥0∞) * C ≤ X) :
    ∑ t ∈ s, (A t + B t) ≤ X := by
  calc ∑ t ∈ s, (A t + B t) ≤ ∑ t ∈ s, (∑ j, A' t j + ∑ j, B' t j) :=
        Finset.sum_le_sum fun t ht => add_le_add (hA t ht) (hB t ht)
    _ = ∑ j, ∑ t ∈ s, (A' t j + B' t j) := by
        simp_rw [← Finset.sum_add_distrib]
        exact Finset.sum_comm
    _ ≤ ∑ _j : J, C := Finset.sum_le_sum fun j _ => hS j
    _ = (Fintype.card J : ℝ≥0∞) * C := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ X := hX

theorem card_pi_fin_mul_ofReal {α : Type*} [DecidableEq α] (T : Finset α) (N : α → ℕ) (C : ℝ) :
    (Fintype.card ((v : ↥T) → Fin (N v)) : ℝ≥0∞) * ENNReal.ofReal C =
      ENNReal.ofReal (C * ∏ v ∈ T, (N v : ℝ)) := by
  have hcard : Fintype.card ((v : ↥T) → Fin (N v)) = ∏ v ∈ T, N v := by
    rw [Fintype.card_pi, ← Finset.prod_coe_sort T]
    simp only [Fintype.card_fin]
  rw [mul_comm C, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _), hcard,
    ← Nat.cast_prod, ENNReal.ofReal_natCast]

end Assembly

end TranslatesGlue

end

p2m_open "AutomorphicForm~continuous_semiLocalEval~continuous_glMap~continuous_semiLocalComponent"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : HeightOneSpectrum (𝓞 K) → ℕ)
        (ρ : ∀ v : HeightOneSpectrum (𝓞 K), Fin (N v) → GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ i : Fin (N v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v i)))⁻¹ * x)
            else φS v) →
      ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
        (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) ≤
        ENNReal.ofReal (C * ∏ v ∈ T, (N v : ℝ)) := by
  intro T ws
  obtain ⟨C, hC0, hC⟩ :=
    AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T ws
  refine ⟨C, hC0, ?_⟩
  intro N ρ φ φf hfact Δφ hΔφ
  have hfact' := fun p : (∀ v : ↥T, Fin (N v)) =>
    TranslatesGlue.isSemiLocalFactorization_sel K L ws S T N ρ φS φ φa φf hfact p
  have hsum := TranslatesGlue.eq_sum_phiSel K L ws S T N ρ φS φ φa φf hfact
  have hS := fun p : (∀ v : ↥T, Fin (N v)) =>
    hC (TranslatesGlue.rhoSel K L ws T N ρ p) (TranslatesGlue.phiSel K L ws T N ρ φf φa p)
      (TranslatesGlue.phifSel K L ws T N ρ φf p) (hfact' p) Δφ hΔφ
  have hADD :=
    AutomorphicForm.lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T
      (TranslatesGlue.phiSel K L ws T N ρ φf φa) φ (fun p => ⟨φa, _, _, hfact' p⟩) hsum
  exact TranslatesGlue.sum_add_le_of_split Δφ _ _ _ _ _ _
    (fun t ht => (hADD t (hΔφ ht)).1) (fun t ht => (hADD t (hΔφ ht)).2) hS
    (TranslatesGlue.card_pi_fin_mul_ofReal T N C).le

end S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates (solution)
