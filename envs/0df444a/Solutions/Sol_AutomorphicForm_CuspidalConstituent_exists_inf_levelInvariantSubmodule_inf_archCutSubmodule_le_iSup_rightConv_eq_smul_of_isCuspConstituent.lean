-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f3be5c84-d726-5055-a5a3-1a96525027c3

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
import Theorems.Thm_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent
open AutomorphicForm.CuspidalSpectrum

open scoped BigOperators

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rightConv_add_left convOp_smul IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant ArchRepAt rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite IsArchBiFinite.of_factorization CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv rightConv_apply rightConv_zero_right rightConv_zero_left IsArchTestFactor isArchTestFactor_zero IsFinTestFactor IsFactorizableTestFn IsLevelSphericalOfType continuous_and_hasCompactSupport_of_isFactorizableTestFn typeSubmodule_inf_typeSubmodule_eq_bot rightConv_mem_archCutSubmodule_of_isArchBiFinite rightTranslate_rightConv_of_isLevelSphericalOfType"
p2m_open "AutomorphicForm"

section RightConvSums

variable (K : Type) [Field K] [NumberField K]

private theorem rightConv_add_right {φ f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) :
    rightConv K φ (fun x => f₁ x + f₂ x) = fun g => rightConv K φ f₁ g + rightConv K φ f₂ g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ {f : AdelicGL2 (𝓞 K) K → ℂ}, Continuous f → HasCompactSupport f →
      ∀ g : AdelicGL2 (𝓞 K) K, MeasureTheory.Integrable (fun x => φ (g * x) * f x)
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro f hf hfc g
    have hc : Continuous fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hf
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x := hfc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext g
  simp only [rightConv_apply, mul_add]
  exact MeasureTheory.integral_add (hint hf₁ hf₁c g) (hint hf₂ hf₂c g)

private theorem continuous_and_hasCompactSupport_finsetSum {ι : Type} (s : Finset ι)
    (z : ι → AdelicGL2 (𝓞 K) K → ℂ) (hz : ∀ j, Continuous (z j) ∧ HasCompactSupport (z j)) :
    Continuous (fun x => ∑ j ∈ s, z j x) ∧ HasCompactSupport (fun x => ∑ j ∈ s, z j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨continuous_const, HasCompactSupport.zero⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ⟨(hz a).1.add ih.1, (hz a).2.add ih.2⟩

private theorem rightConv_finsetSum_right {ι : Type} (s : Finset ι) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (z : ι → AdelicGL2 (𝓞 K) K → ℂ)
    (hz : ∀ j, Continuous (z j) ∧ HasCompactSupport (z j)) :
    rightConv K φ (fun x => ∑ j ∈ s, z j x) = fun g => ∑ j ∈ s, rightConv K φ (z j) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rightConv_zero_right K φ
  | insert a s ha ih =>
    have hs := continuous_and_hasCompactSupport_finsetSum K s z hz
    simp only [Finset.sum_insert ha]
    rw [rightConv_add_right K hφ (hz a).1 (hz a).2 hs.1 hs.2, ih]

end RightConvSums

section TypePieceCongr

variable {H G : Type*} [Group H] [Group G]
variable {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem typeSubmodule_le_of_equiv (ι : H →* G) {ρ : Representation ℂ H W}
    {ρ' : Representation ℂ H W'} (e : ρ.Equiv ρ') : typeSubmodule ι ρ' ≤ typeSubmodule ι ρ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, v, rfl⟩
  have hS : IsRightEquivariant ι ρ (T ∘ₗ e.toLinearMap) := by
    intro k u x
    have hek : e (ρ k u) = ρ' k (e u) :=
      Representation.IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap k u
    simp only [LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [hek]
    exact hT k (e u) x
  have hv : T v = (T ∘ₗ e.toLinearMap) (e.symm v) := by
    simp only [LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap,
      Representation.Equiv.apply_symm_apply]
  rw [hv]
  exact mem_typeSubmodule_of_isRightEquivariant hS _

private theorem typeSubmodule_eq_of_equiv (ι : H →* G) {ρ : Representation ℂ H W}
    {ρ' : Representation ℂ H W'} (e : ρ.Equiv ρ') : typeSubmodule ι ρ = typeSubmodule ι ρ' :=
  le_antisymm (typeSubmodule_le_of_equiv ι e.symm) (typeSubmodule_le_of_equiv ι e)

end TypePieceCongr

section ArchCutCongr

variable (F : Type) [Field F] [NumberField F]

private theorem archTypeSubmoduleAt_eq_of_equiv (w : InfinitePlace F) {τ τ' : ArchRepAt F w}
    (e : τ.ρ.Equiv τ'.ρ) : archTypeSubmoduleAt F w τ = archTypeSubmoduleAt F w τ' :=
  typeSubmodule_eq_of_equiv (rowIsometryInclAt₀ F w) e

private theorem archCutSubmodule_eq_of_forall_equiv {τ τ' : ∀ w : InfinitePlace F, ArchRepAt F w}
    (e : ∀ w, (τ w).ρ.Equiv (τ' w).ρ) :
    archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) =
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τ' w⟩ : AutomorphicForm.ArchTypeFamily F) := by
  unfold archCutSubmodule
  exact iInf_congr fun w => iSup_congr fun _ => archTypeSubmoduleAt_eq_of_equiv F w (e w)

end ArchCutCongr

section TestFnSums

open NumberField.AdelicLevel IsDedekindDomain
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

namespace IsArchTestFactor
private theorem _root_.AutomorphicForm.IsArchTestFactor.add {fa fb : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (ha : IsArchTestFactor F fa) (hb : IsArchTestFactor F fb) :
    IsArchTestFactor F (fun x => fa x + fb x) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hca⟩ := ha
  obtain ⟨⟨Ψ, hΨ, hfb⟩, hcb⟩ := hb
  refine ⟨⟨fun e => Φ e + Ψ e, hΦ.add hΨ, fun g => ?_⟩, ?_⟩
  · simp only [hfa g, hfb g]
  · exact hca.add hcb

end IsArchTestFactor
p2m_export "AutomorphicForm" "IsArchTestFactor.add"
private theorem isArchTestFactor_finsetSum {ι : Type} (s : Finset ι)
    (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (h : ∀ j, IsArchTestFactor F (fa j)) :
    IsArchTestFactor F (fun x => ∑ j ∈ s, fa j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isArchTestFactor_zero F
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsArchTestFactor.add F (h a) ih

private theorem isFinTestFactor_indicator_of_isClopen_of_isCompact
    {S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hS : IsClopen S) (hSc : IsCompact S) :
    IsFinTestFactor F (Set.indicator S (fun _ => (1 : ℂ))) := by
  refine ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ S
    · refine ⟨S, hS.isOpen, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · refine ⟨Sᶜ, hS.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · rw [hasCompactSupport_def]
    exact hSc.of_isClosed_subset isClosed_closure
      (closure_minimal Set.support_indicator_subset hS.isClosed)

private theorem image_glFin_levelOne_inf_finiteAdelicGL2Subgroup (N : Ideal (𝓞 F)) :
    glFin (𝓞 F) F ''
        ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
          Set (AdelicGL2 (𝓞 F) F)) =
      (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext b
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (Subgroup.mem_inf.1 hg).1
  · intro hb
    refine ⟨AdelicDock.finEmbed (𝓞 F) F b, Subgroup.mem_inf.2 ⟨?_, ?_⟩,
      AdelicDock.glFin_finEmbed (𝓞 F) F b⟩
    · exact (AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F (N := N) b).2 hb
    · exact (mem_finiteAdelicGL2Subgroup_iff F _).2 (AdelicDock.glArch_finEmbed (𝓞 F) F b)

private theorem isFinTestFactor_indicator_image_glFin_levelOne_inf (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsFinTestFactor F (Set.indicator (glFin (𝓞 F) F ''
      ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
        Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
  rw [image_glFin_levelOne_inf_finiteAdelicGL2Subgroup F N]
  exact isFinTestFactor_indicator_of_isClopen_of_isCompact F
    ⟨isClosed_finiteLevelOne (𝓞 F) F N, isOpen_finiteLevelOne (𝓞 F) F hN⟩
    (isCompact_finiteLevelOne (𝓞 F) F N)

private theorem isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator {ι : Type} (s : Finset ι)
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hU : IsFinTestFactor F
      (Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))))
    (z : ι → AdelicGL2 (𝓞 F) F → ℂ) (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : ∀ j, IsArchTestFactor F (fa j))
    (hz : ∀ j, ∀ g : AdelicGL2 (𝓞 F) F, z j g = fa j (glArch (𝓞 F) F g) *
      Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
        (glFin (𝓞 F) F g)) :
    IsFactorizableTestFn F (fun g => ∑ j ∈ s, z j g) :=
  ⟨fun x => ∑ j ∈ s, fa j x,
    Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)),
    isArchTestFactor_finsetSum F s fa hfa, hU, fun g => by simp only [hz, Finset.sum_mul]⟩

private theorem isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator_levelOne_inf {ι : Type} (s : Finset ι)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hUN : U = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (z : ι → AdelicGL2 (𝓞 F) F → ℂ) (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : ∀ j, IsArchTestFactor F (fa j))
    (hz : ∀ j, ∀ g : AdelicGL2 (𝓞 F) F, z j g = fa j (glArch (𝓞 F) F g) *
      Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
        (glFin (𝓞 F) F g)) :
    IsFactorizableTestFn F (fun g => ∑ j ∈ s, z j g) := by
  subst hUN
  exact isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator F s _
    (isFinTestFactor_indicator_image_glFin_levelOne_inf F N hN) z fa hfa hz

end TestFnSums

end AutomorphicForm

section IsotypicTransport

variable {H G : Type*} [Group H] [Group G]

private def rightTranslationRep (ι : H →* G) : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun f x => f (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' k₁ k₂ := by
    ext f x
    simp [mul_assoc]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private def intertwiningOfEquivariant {ι : H →* G} {ρ : Representation ℂ H W} {T : W →ₗ[ℂ] (G → ℂ)}
    (hT : IsRightEquivariant ι ρ T) : ρ.IntertwiningMap (rightTranslationRep ι) where
  toLinearMap := T
  isIntertwining' k := by
    ext v x
    exact hT k v x

set_option backward.isDefEq.respectTransparency false in

private abbrev asModuleMap (ι : H →* G) (ρ : Representation ℂ H W)
    (φ : ρ.IntertwiningMap (rightTranslationRep ι)) :
    ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι) φ

set_option backward.isDefEq.respectTransparency false in

private def nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) :
    Set (Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule) :=
  {m | ∃ φ : ρ.IntertwiningMap (rightTranslationRep ι), LinearMap.range (asModuleMap ι ρ φ) = m ∧ m ≠ ⊥}

set_option backward.isDefEq.respectTransparency false in

private theorem nonzeroRanges_equiv (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible] :
    ∀ m ∈ nonzeroRanges ι ρ, Nonempty (m ≃ₗ[MonoidAlgebra ℂ H] ρ.asModule) := by
  rintro m ⟨φ, rfl, hm⟩
  rcases LinearMap.injective_or_eq_zero (asModuleMap ι ρ φ) with hinj | hzero
  · exact ⟨(LinearEquiv.ofInjective _ hinj).symm⟩
  · exact absurd (by rw [hzero, LinearMap.range_zero]) hm

set_option backward.isDefEq.respectTransparency false in

private theorem mem_sSup_nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) :
    (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ) := by
  refine Submodule.span_induction
    (p := fun f _ => (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hle : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) ≤ sSup (nonzeroRanges ι ρ) := by
      by_cases hbot : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_sSup ⟨intertwiningOfEquivariant hT, rfl, hbot⟩
    exact hle (LinearMap.mem_range_self (asModuleMap ι ρ (intertwiningOfEquivariant hT)) (ρ.asModuleEquiv.symm v))
  · simp
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (sSup (nonzeroRanges ι ρ)).add_mem hu hw
  · intro c _ _ hu
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact (sSup (nonzeroRanges ι ρ)).smul_mem _ hu

set_option backward.isDefEq.respectTransparency false in

private theorem isRightEquivariant_of_intertwining {ι : H →* G} {ρ : Representation ℂ H W}
    (ψ : ρ.IntertwiningMap (rightTranslationRep ι)) : IsRightEquivariant ι ρ ψ.toLinearMap := by
  intro k v x
  exact congrFun (LinearMap.congr_fun (ψ.isIntertwining' k) v) x

set_option backward.isDefEq.respectTransparency false in

private theorem exists_isRightEquivariant_of_simple_le (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible]
    (m : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule) [IsSimpleModule (MonoidAlgebra ℂ H) m]
    (hm : m ≤ sSup (nonzeroRanges ι ρ)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧
      (∀ v : W, (rightTranslationRep ι).asModuleEquiv.symm (T v) ∈ m) ∧
      ∀ g : (rightTranslationRep ι).asModule, g ∈ m → ∃ v : W, T v = (rightTranslationRep ι).asModuleEquiv g := by
  haveI : ∀ r : nonzeroRanges ι ρ, IsSimpleModule (MonoidAlgebra ℂ H) r :=
    fun r => IsSimpleModule.congr (nonzeroRanges_equiv ι ρ r r.2).some
  obtain ⟨r, hr, ⟨e₁⟩⟩ := Submodule.linearEquiv_of_le_sSup m (nonzeroRanges ι ρ) hm
  obtain ⟨e₂⟩ := nonzeroRanges_equiv ι ρ r hr
  let e : ρ.asModule ≃ₗ[MonoidAlgebra ℂ H] m := (e₁.trans e₂).symm
  let L : ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule := m.subtype ∘ₗ e.toLinearMap
  let ψ : ρ.IntertwiningMap (rightTranslationRep ι) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι)).symm L
  have hψ : ∀ v : W,
      ψ.toLinearMap v = (rightTranslationRep ι).asModuleEquiv (L (ρ.asModuleEquiv.symm v)) := fun _ => rfl
  refine ⟨ψ.toLinearMap, isRightEquivariant_of_intertwining ψ, fun v => ?_, fun g hg => ?_⟩
  · rw [hψ, LinearEquiv.symm_apply_apply]
    exact (e (ρ.asModuleEquiv.symm v)).2
  · refine ⟨ρ.asModuleEquiv (e.symm ⟨g, hg⟩), ?_⟩
    have h : L (e.symm ⟨g, hg⟩) = g := by
      show ((e (e.symm ⟨g, hg⟩) : m) : (rightTranslationRep ι).asModule) = g
      rw [LinearEquiv.apply_symm_apply]
    rw [hψ, LinearEquiv.symm_apply_apply, h]

private theorem asAlgebraHom_mem (ι : H →* G) (P : Set (G → ℂ))
    (hP_tr : ∀ (k : H), ∀ f ∈ P, (fun x => f (x * ι k)) ∈ P) (hP_add : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P)
    (hP_smul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P) (r : MonoidAlgebra ℂ H) {f : G → ℂ} (hf : f ∈ P) :
    (rightTranslationRep ι).asAlgebraHom r f ∈ P := by
  refine MonoidAlgebra.induction_on (motive := fun r => (rightTranslationRep ι).asAlgebraHom r f ∈ P) r
    (fun k => ?_) (fun r₁ r₂ h₁ h₂ => ?_) (fun c r h => ?_)
  · show (rightTranslationRep ι).asAlgebraHom (MonoidAlgebra.of ℂ H k) f ∈ P
    rw [Representation.asAlgebraHom_of]
    exact hP_tr k f hf
  · show (rightTranslationRep ι).asAlgebraHom (r₁ + r₂) f ∈ P
    rw [map_add, LinearMap.add_apply]
    exact hP_add _ h₁ _ h₂
  · show (rightTranslationRep ι).asAlgebraHom (c • r) f ∈ P
    rw [map_smul, LinearMap.smul_apply]
    exact hP_smul c _ h

private theorem isSemisimpleModule_of_le {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N Q : Submodule R M} [IsSemisimpleModule R Q] (h : N ≤ Q) : IsSemisimpleModule R N :=
  IsSemisimpleModule.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective _)

private theorem induction_of_isSemisimpleModule {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (N : Submodule R V) [IsSemisimpleModule R N] {motive : V → Prop}
    (hsimple : ∀ m : Submodule R V, IsSimpleModule R m → m ≤ N → ∀ y ∈ m, motive y) (hzero : motive 0)
    (hadd : ∀ y₁ y₂ : V, y₁ ∈ N → y₂ ∈ N → motive y₁ → motive y₂ → motive (y₁ + y₂))
    {x : V} (hx : x ∈ N) : motive x := by
  have hmem : (⟨x, hx⟩ : N) ∈ sSup {m : Submodule R N | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    exact Submodule.mem_top
  rw [sSup_eq_iSup'] at hmem
  refine Submodule.iSup_induction (motive := fun y : N => motive (y : V)) _ hmem ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    haveI : IsSimpleModule R m := hm
    change y ∈ m at hy
    exact hsimple (m.map N.subtype)
      (IsSimpleModule.congr (Submodule.equivMapOfInjective N.subtype N.injective_subtype m).symm)
      (Submodule.map_subtype_le (p := N) m) (y : V) (Submodule.mem_map_of_mem hy)
  · exact hzero
  · intro y₁ y₂ h₁ h₂
    exact hadd (y₁ : V) (y₂ : V) y₁.2 y₂.2 h₁ h₂

set_option backward.isDefEq.respectTransparency false in

private theorem map_mem_typeSubmodule (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible]
    (P : Set (G → ℂ)) (hP_tr : ∀ (k : H), ∀ f ∈ P, (fun x => f (x * ι k)) ∈ P)
    (hP_add : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P) (hP_smul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P)
    (A : (G → ℂ) → (G → ℂ)) (hA_add : ∀ f ∈ P, ∀ g ∈ P, A (f + g) = A f + A g)
    (hA_smul : ∀ (c : ℂ) (f : G → ℂ), A (c • f) = c • A f) (hA_zero : A 0 = 0)
    (hA_tr : ∀ (k : H) (f : G → ℂ), A (fun x => f (x * ι k)) = fun x => A f (x * ι k))
    {f : G → ℂ} (hfP : f ∈ P) (hf : f ∈ typeSubmodule ι ρ) : A f ∈ typeSubmodule ι ρ := by
  haveI simple_ranges : ∀ r : nonzeroRanges ι ρ, IsSimpleModule (MonoidAlgebra ℂ H) r :=
    fun r => IsSimpleModule.congr (nonzeroRanges_equiv ι ρ r r.2).some
  haveI hsemi : IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (nonzeroRanges ι ρ)) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
      (p := fun m : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule => m)
      (fun m hm => by
        haveI := simple_ranges ⟨m, hm⟩
        exact inferInstance)
  set f' : (rightTranslationRep ι).asModule := (rightTranslationRep ι).asModuleEquiv.symm f with hf'
  let N : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule := Submodule.span (MonoidAlgebra ℂ H) {f'}
  have hNQ : N ≤ sSup (nonzeroRanges ι ρ) :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 (mem_sSup_nonzeroRanges ι ρ hf))
  have hNP : ∀ g ∈ N, (rightTranslationRep ι).asModuleEquiv g ∈ P := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => (rightTranslationRep ι).asModuleEquiv g ∈ P) ?_ ?_ ?_ ?_ hg
    · intro g hg
      rcases Set.mem_singleton_iff.1 hg with rfl
      show (rightTranslationRep ι).asModuleEquiv f' ∈ P
      rw [hf', LinearEquiv.apply_symm_apply]
      exact hfP
    · simpa using hP_smul (0 : ℂ) f hfP
    · intro _ _ _ _ h₁ h₂
      rw [map_add]
      exact hP_add _ h₁ _ h₂
    · intro r _ _ h
      rw [Representation.asModuleEquiv_map_smul]
      exact asAlgebraHom_mem ι P hP_tr hP_add hP_smul r h
  haveI hNsemi : IsSemisimpleModule (MonoidAlgebra ℂ H) N := isSemisimpleModule_of_le hNQ
  have hind : A ((rightTranslationRep ι).asModuleEquiv f') ∈ typeSubmodule ι ρ := by
    refine induction_of_isSemisimpleModule N
      (motive := fun g => A ((rightTranslationRep ι).asModuleEquiv g) ∈ typeSubmodule ι ρ) ?_ ?_ ?_
      (Submodule.mem_span_singleton_self f')
    · intro m hm hmN y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) m := hm
      obtain ⟨T, hT, hTm, hsurj⟩ := exists_isRightEquivariant_of_simple_le ι ρ m (hmN.trans hNQ)
      obtain ⟨v, hv⟩ := hsurj y hy
      show A ((rightTranslationRep ι).asModuleEquiv y) ∈ typeSubmodule ι ρ
      rw [← hv]
      have hTP : ∀ u : W, T u ∈ P := fun u => by
        have h := hNP _ (hmN (hTm u))
        rwa [LinearEquiv.apply_symm_apply] at h
      let TA : W →ₗ[ℂ] (G → ℂ) :=
        { toFun := fun u => A (T u)
          map_add' := fun u u' => by
            show A (T (u + u')) = A (T u) + A (T u')
            rw [map_add, hA_add _ (hTP u) _ (hTP u')]
          map_smul' := fun c u => by
            show A (T (c • u)) = c • A (T u)
            rw [map_smul, hA_smul] }
      have hTA : IsRightEquivariant ι ρ TA := by
        intro k u x
        show A (T (ρ k u)) x = A (T u) (x * ι k)
        rw [show T (ρ k u) = fun y => T u (y * ι k) from funext (hT k u), hA_tr k (T u)]
      exact mem_typeSubmodule_of_isRightEquivariant hTA v
    · show A ((rightTranslationRep ι).asModuleEquiv 0) ∈ typeSubmodule ι ρ
      rw [map_zero, hA_zero]
      exact Submodule.zero_mem _
    · intro y₁ y₂ hy₁ hy₂ h₁ h₂
      show A ((rightTranslationRep ι).asModuleEquiv (y₁ + y₂)) ∈ typeSubmodule ι ρ
      rw [map_add, hA_add _ (hNP _ hy₁) _ (hNP _ hy₂)]
      exact Submodule.add_mem _ h₁ h₂
  rwa [hf', LinearEquiv.apply_symm_apply] at hind

end IsotypicTransport

namespace AutomorphicForm p2m_export "AutomorphicForm" "rightConv_add_left convOp_smul IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant ArchRepAt rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite IsArchBiFinite.of_factorization CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv rightConv_apply rightConv_zero_right rightConv_zero_left IsArchTestFactor isArchTestFactor_zero IsFinTestFactor IsFactorizableTestFn IsLevelSphericalOfType continuous_and_hasCompactSupport_of_isFactorizableTestFn typeSubmodule_inf_typeSubmodule_eq_bot rightConv_mem_archCutSubmodule_of_isArchBiFinite rightTranslate_rightConv_of_isLevelSphericalOfType" end AutomorphicForm
p2m_open_scoped "AutomorphicForm" in

private theorem AutomorphicForm.rightConv_mem_archTypeSubmoduleAt_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (σ : ArchRepAt F w) [σ.ρ.IsIrreducible]
    (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)) (z : AdelicGL2 (𝓞 F) F → ℂ)
    (hzT : IsFactorizableTestFn F z) (hz : IsLevelSphericalOfType F tys U z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ : φ ∈ archTypeSubmoduleAt F w σ) :
    rightConv F φ z ∈ archTypeSubmoduleAt F w σ := by
  obtain ⟨hzc, hzs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F z hzT
  show rightConv F φ z ∈ typeSubmodule (rowIsometryInclAt₀ F w) σ.ρ
  refine map_mem_typeSubmodule (rowIsometryInclAt₀ F w) σ.ρ {u : AdelicGL2 (𝓞 F) F → ℂ | Continuous u}
    (fun k u hu => (hu : Continuous u).comp (continuous_id.mul continuous_const))
    (fun u hu u' hu' => (hu : Continuous u).add hu') (fun c u hu => (hu : Continuous u).const_smul c)
    (fun u => rightConv F u z) (fun u hu u' hu' => rightConv_add_left F hu hu' hzc hzs)
    (fun c u => convOp_smul F z c u) (rightConv_zero_left F z) (fun k u => ?_) hφc hφ
  exact (rightTranslate_rightConv_of_isLevelSphericalOfType F tys U z hz w k u).symm

private theorem mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single (F : Type) [Field F] [NumberField F]
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (w : InfinitePlace F) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : f ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F)) :
    f ∈ archTypeSubmoduleAt F w (τ w) := by
  have h1 := (mem_archCutSubmodule_iff F _ f).1 hf w
  have h2 : (⨆ i : Fin ((⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F).card w),
      archTypeSubmoduleAt F w ((⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F).rep w i)) ≤
        archTypeSubmoduleAt F w (τ w) :=
    iSup_le fun _ => le_rfl
  exact h2 h1

p2m_open_scoped "AutomorphicForm" in
private theorem AutomorphicForm.rightConv_eq_zero_of_isEmpty_equiv
    (F : Type) [Field F] [NumberField F]
    (σ τ : ∀ w : InfinitePlace F, ArchRepAt F w) (w₀ : InfinitePlace F)
    (hσ : (σ w₀).ρ.IsIrreducible) (hτ : (τ w₀).ρ.IsIrreducible)
    (hne : IsEmpty ((σ w₀).ρ.Equiv ((τ w₀).ρ)))
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (z : AdelicGL2 (𝓞 F) F → ℂ) (hzT : IsFactorizableTestFn F z)
    (hz : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) U z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφ : φ ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => σ w⟩ : ArchTypeFamily F)) :
    rightConv F φ z = 0 := by
  have hz' := hz
  obtain ⟨fa, -, hB, -, hfeq⟩ := hz'
  have hbi : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) z :=
    IsArchBiFinite.of_factorization F (fa := fa)
      (ff := Set.indicator (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) fun _ => (1 : ℂ)) hfeq hB
  have hτcut : rightConv F φ z ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) :=
    rightConv_mem_archCutSubmodule_of_isArchBiFinite F _ φ hφc z hzT hbi
  have hτpiece : rightConv F φ z ∈ archTypeSubmoduleAt F w₀ (τ w₀) :=
    mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single F τ w₀ hτcut
  have hσpiece : rightConv F φ z ∈ archTypeSubmoduleAt F w₀ (σ w₀) :=
    rightConv_mem_archTypeSubmoduleAt_of_isLevelSphericalOfType F w₀ (σ w₀) _ U z hzT hz φ hφc
      (mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single F σ w₀ hφ)
  have hmeet : rightConv F φ z ∈ typeSubmodule (rowIsometryInclAt₀ F w₀) (σ w₀).ρ ⊓
      typeSubmodule (rowIsometryInclAt₀ F w₀) (τ w₀).ρ :=
    Submodule.mem_inf.2 ⟨hσpiece, hτpiece⟩
  rw [typeSubmodule_inf_typeSubmodule_eq_bot (rowIsometryInclAt₀ F w₀) (σ w₀).ρ (τ w₀).ρ hne] at hmeet
  exact (Submodule.mem_bot ℂ).1 hmeet

namespace EigenCapture

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_of_mem_cuspKFiniteSubmodule {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · exact fun _ h => h.2.1
  · exact continuous_const
  · exact fun _ _ _ _ hu hv => hu.add hv
  · exact fun c _ _ hu => hu.const_smul c

private def piece (pins : CarrierPins F) (N : Ideal (𝓞 F)) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (κ : ∀ w : InfinitePlace F, ArchRepAt F w) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  V ⊓ levelInvariantSubmodule F pins N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => κ w⟩ : ArchTypeFamily F)

private theorem piece_congr (pins : CarrierPins F) (N : Ideal (𝓞 F))
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) {κ κ' : ∀ w : InfinitePlace F, ArchRepAt F w}
    (e : ∀ w, (κ w).ρ.Equiv (κ' w).ρ) : piece F pins N V κ = piece F pins N V κ' := by
  unfold piece
  rw [archCutSubmodule_eq_of_forall_equiv F e]

private theorem mem_inf_inf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q r : Submodule R M} {x : M} : x ∈ p ⊓ q ⊓ r ↔ (x ∈ p ∧ x ∈ q) ∧ x ∈ r :=
  Iff.rfl

end EigenCapture

open EigenCapture in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ)
      (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ∀ φ ∈ E i, φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧ rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by
  have _ := hX
  classical
  obtain ⟨σ, hσ⟩ := exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V hV
  obtain ⟨m, τs, hirr, hsplit⟩ :=
    exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep F c u d₁ d₂ T ξ N tys V hV.1

  let X : Fin m → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun j =>
    piece F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N V (τs j)
  let P : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := (Finset.univ.filter fun j => X j ≠ ⊥).image X
  have hP : ∀ p ∈ P, ∃ j, X j ≠ ⊥ ∧ X j = p := fun p hp => by
    obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp hp
    exact ⟨j, (Finset.mem_filter.mp hj).2, hjp⟩
  choose idx hidx_ne hidx_eq using hP

  choose z hzT hzsph hzflat _hzpres hzne using fun k : Fin P.card =>
    exists_rightConv_ne_zero_of_ne_bot F c u d₁ d₂ T ξ σ hσ N hN
      (τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2))
      (hirr (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2)) V hV
      (hidx_ne (P.equivFin.symm k).1 (P.equivFin.symm k).2)
  choose lam hlam using fun k : Fin P.card =>
    exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ N hN
      (τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2))
      (hirr (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2)) V hV (z k) (hzT k) (hzsph k)
      (hzflat k)
  choose fa hfa _hfaB _hfaconj hfac using fun k : Fin P.card => hzsph k
  have hzc : ∀ k, Continuous (z k) ∧ HasCompactSupport (z k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn F (z k) (hzT k)

  have hlam0 : ∀ k, (lam k : ℂ) ≠ 0 := fun k h0 => by
    obtain ⟨φ₀, hφ₀, hne0⟩ := hzne k
    exact hne0 (by rw [hlam k φ₀ hφ₀, h0, zero_smul])

  have hsep : ∀ k k' : Fin P.card, k' ≠ k →
      ∃ w₀, IsEmpty ((τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) w₀).ρ.Equiv
        ((τs (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) w₀).ρ)) := by
    intro k k' hk'
    by_contra hno
    apply hk'
    have hall : ∀ w₀, Nonempty ((τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) w₀).ρ.Equiv
        ((τs (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) w₀).ρ)) :=
      fun w₀ => not_isEmpty_iff.mp fun h => hno ⟨w₀, h⟩
    have hXX : X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) =
        X (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) :=
      piece_congr F _ N V fun w₀ => (hall w₀).some
    exact (P.equivFin.symm.injective (Subtype.ext
      (((hidx_eq _ _).symm.trans hXX).trans (hidx_eq _ _)))).symm

  have hact : ∀ k, ∀ φ ∈ X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2),
      rightConv F φ (fun g => ∑ k' ∈ Finset.univ, z k' g) = (lam k : ℂ) • φ := by
    intro k φ hφ
    have hφV : φ ∈ V := (mem_inf_inf.mp hφ).1.1
    have hφc : Continuous φ := continuous_of_mem_cuspKFiniteSubmodule F (hV.1.le hφV)
    rw [rightConv_finsetSum_right F Finset.univ hφc z hzc]
    funext g
    have hvan : ∀ k' ∈ Finset.univ, k' ≠ k → rightConv F φ (z k') g = 0 := by
      intro k' _ hk'
      obtain ⟨w₀, hw₀⟩ := hsep k k' hk'
      rw [rightConv_eq_zero_of_isEmpty_equiv F _ _ w₀ (hirr _ w₀) (hirr _ w₀) hw₀ _ (z k') (hzT k') (hzsph k')
        φ hφc (mem_inf_inf.mp hφ).2]
      rfl
    rw [Finset.sum_eq_single k hvan (fun h => absurd (Finset.mem_univ k) h), hlam k φ hφ]

  have hfT : IsFactorizableTestFn F (fun g => ∑ k ∈ Finset.univ, z k g) :=
    isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator_levelOne_inf F Finset.univ N hN _ rfl z fa hfa hfac

  have hdom : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ k : Fin P.card, X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) := by
    refine hsplit.trans (iSup_le fun j => ?_)
    by_cases hj : X j = ⊥
    · exact (le_of_eq hj).trans bot_le
    · have hp : X j ∈ P := Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
      refine le_iSup_of_le (P.equivFin ⟨X j, hp⟩) (le_of_eq ?_)
      exact ((hidx_eq _ _).trans (congrArg Subtype.val (P.equivFin.symm_apply_apply ⟨X j, hp⟩))).symm
  exact ⟨fun g => ∑ k ∈ Finset.univ, z k g, hfT, P.card, fun k => (lam k : ℂ), hlam0,
    fun k => X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2),
    fun k φ hφ => ⟨hV.1.le (mem_inf_inf.mp hφ).1.1, hact k φ hφ⟩, hdom⟩

end

#print axioms solution

end S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent (solution)
