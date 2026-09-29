-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/eb794a82-91a7-566b-be08-95dc973cc99f

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isLevelSphericalOfType_ofChar_flat
import Theorems.Thm_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate

namespace R5cGlue

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F) 1

  have : NumberField.TateGlobal.ideleNorm F 1 * (NumberField.TateGlobal.ideleNorm F 1 - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact absurd h0 hpos.ne'
  · linarith

theorem ideleNorm_inv (x : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F x⁻¹ = (NumberField.TateGlobal.ideleNorm F x)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) x⁻¹ x
  rw [inv_mul_cancel, ideleNorm_one] at h
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F) x
  field_simp
  linarith [h]

theorem flat_flat (σ : ℝ) (f : AdelicGL2 (𝓞 F) F → ℂ) : flat F σ (flat F σ f) = f := by
  funext y
  simp only [flat, map_mul, Complex.conj_conj, Complex.conj_ofReal, inv_inv, map_inv]
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F) (Matrix.GeneralLinearGroup.det y)
  rw [ideleNorm_inv, Real.inv_rpow hpos.le, mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos _).ne', Complex.ofReal_one, mul_one]

theorem flat_add_smul (σ : ℝ) (f g : AdelicGL2 (𝓞 F) F → ℂ) (a b : ℂ) :
    flat F σ (a • f + b • g) = conj a • flat F σ f + conj b • flat F σ g := by
  funext y
  simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem rightConv_add_smul_right {φ f g : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (a b : ℂ) :
    rightConv F φ (a • f + b • g) = a • rightConv F φ f + b • rightConv F φ g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ {k : AdelicGL2 (𝓞 F) F → ℂ}, Continuous k → HasCompactSupport k → ∀ x : AdelicGL2 (𝓞 F) F,
      MeasureTheory.Integrable (fun y => φ (x * y) * k y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro k hk hkc x
    have hc : Continuous fun y : AdelicGL2 (𝓞 F) F => φ (x * y) * k y :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hk
    have hs : HasCompactSupport fun y : AdelicGL2 (𝓞 F) F => φ (x * y) * k y := hkc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext x
  simp only [rightConv_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsplit : (fun y => φ (x * y) * (a * f y + b * g y)) =
      fun y => a * (φ (x * y) * f y) + b * (φ (x * y) * g y) := by
    funext y; ring
  rw [hsplit, MeasureTheory.integral_add ((hint hf hfc x).const_mul a) ((hint hg hgc x).const_mul b),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

open scoped Classical in
theorem isArchTestFactor_add_smul {fa ga : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (a b : ℂ)
    (hfa : IsArchTestFactor F fa) (hga : IsArchTestFactor F ga) : IsArchTestFactor F (a • fa + b • ga) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hfac⟩ := hfa
  obtain ⟨⟨Ψ, hΨ, hgaΨ⟩, hgac⟩ := hga
  refine ⟨⟨fun m => a * Φ m + b * Ψ m, (contDiff_const.mul hΦ).add (contDiff_const.mul hΨ), fun x => ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfaΦ, hgaΨ]
  · have ha : HasCompactSupport (a • fa) := by
      have h__af := (HasCompactSupport.smul_left (f := fun _ => a) hfac)
      simp at h__af
      exact h__af
    have hb : HasCompactSupport (b • ga) := by
      have h__af := (HasCompactSupport.smul_left (f := fun _ => b) hgac)
      simp at h__af
      exact h__af
    exact ha.add hb

theorem isArchFactorBiFinite_add_smul (tys : ArchTypeFamily F) {fa ga : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (a b : ℂ) (hfa : IsArchFactorBiFinite F tys fa) (hga : IsArchFactorBiFinite F tys ga) :
    IsArchFactorBiFinite F tys (a • fa + b • ga) := by
  obtain ⟨hl, hr⟩ := hfa
  obtain ⟨hl', hr'⟩ := hga
  refine ⟨?_, Submodule.add_mem _ (Submodule.smul_mem _ a hr) (Submodule.smul_mem _ b hr')⟩
  have : (fun x => (a • fa + b • ga) x⁻¹) = a • (fun x => fa x⁻¹) + b • (fun x => ga x⁻¹) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ a hl) (Submodule.smul_mem _ b hl')

theorem isLevelSphericalOfType_add_smul (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f g : AdelicGL2 (𝓞 F) F → ℂ) (a b : ℂ)
    (hf : IsLevelSphericalOfType F tys U f) (hg : IsLevelSphericalOfType F tys U g) :
    IsLevelSphericalOfType F tys U (a • f + b • g) := by
  obtain ⟨fa, hfa, hbf, hconj, hf⟩ := hf
  obtain ⟨ga, hga, hbg, hconj', hg⟩ := hg
  refine ⟨a • fa + b • ga, isArchTestFactor_add_smul F a b hfa hga, isArchFactorBiFinite_add_smul F tys a b hbf hbg,
    fun w k x => ?_, fun y => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, hconj, hconj']
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf y, hg y]
    ring

theorem isIrreducible_ofChar {w : InfinitePlace F} (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    (ArchRepAt.ofChar F χ).ρ.IsIrreducible := by
  show (charRep χ).IsIrreducible
  unfold Representation.IsIrreducible
  haveI : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  have key : ∀ W : Subrepresentation (charRep χ), W = ⊥ ∨ W = ⊤ := by
    intro W
    rcases eq_bot_or_eq_top W.toSubmodule with h | h
    · left; apply Subrepresentation.toSubmodule_injective; exact h
    · right; apply Subrepresentation.toSubmodule_injective; exact h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := key }
  have h' := congrArg Subrepresentation.toSubmodule h
  change (⊥ : Submodule ℂ (Fin 1 → ℂ)) = ⊤ at h'
  exact bot_ne_top h'

end R5cGlue

noncomputable section

namespace R5cGlue
namespace LevelAux

variable (F : Type) [Field F] [NumberField F]

private def finMatFun (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, m i j)

private def archMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (a i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem finMatFun_map_arch (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (finMatFun F m).map (adeleArch (𝓞 F) F) = 1 := by
  ext i j; rfl

private theorem finMatFun_map_fin (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (finMatFun F m).map (adeleFin (𝓞 F) F) = m := by
  ext i j; rfl

private theorem archMatFun_map_arch (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (archMatFun F a).map (adeleArch (𝓞 F) F) = a := by
  ext i j; rfl

private theorem archMatFun_map_fin (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (archMatFun F a).map (adeleFin (𝓞 F) F) = 1 := by
  ext i j; rfl

private theorem matrix_ext_of_map {M M' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (h₁ : M.map (adeleArch (𝓞 F) F) = M'.map (adeleArch (𝓞 F) F))
    (h₂ : M.map (adeleFin (𝓞 F) F) = M'.map (adeleFin (𝓞 F) F)) : M = M' := by
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j

private def finMat :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := finMatFun F
  map_one' := matrix_ext_of_map F
    (by rw [finMatFun_map_arch, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [finMatFun_map_fin, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' m m' := matrix_ext_of_map F
    (by rw [Matrix.map_mul, finMatFun_map_arch, finMatFun_map_arch, finMatFun_map_arch, Matrix.mul_one])
    (by rw [Matrix.map_mul, finMatFun_map_fin, finMatFun_map_fin, finMatFun_map_fin])

private def archMat :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := archMatFun F
  map_one' := matrix_ext_of_map F
    (by rw [archMatFun_map_arch, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [archMatFun_map_fin, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a a' := matrix_ext_of_map F
    (by rw [Matrix.map_mul, archMatFun_map_arch, archMatFun_map_arch, archMatFun_map_arch])
    (by rw [Matrix.map_mul, archMatFun_map_fin, archMatFun_map_fin, archMatFun_map_fin, Matrix.mul_one])

@[scoped simp] private theorem finMat_apply (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finMat F m = finMatFun F m := rfl

@[scoped simp] private theorem archMat_apply (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    archMat F a = archMatFun F a := rfl

private theorem archMatFun_mul_finMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    archMatFun F a * finMatFun F m = fun i j => (a i j, m i j) := by
  refine matrix_ext_of_map F ?_ ?_
  · rw [Matrix.map_mul, archMatFun_map_arch, finMatFun_map_arch, Matrix.mul_one]; ext i j; rfl
  · rw [Matrix.map_mul, archMatFun_map_fin, finMatFun_map_fin, Matrix.one_mul]; ext i j; rfl

private theorem finMatFun_mul_archMatFun (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finMatFun F m * archMatFun F a = fun i j => (a i j, m i j) := by
  refine matrix_ext_of_map F ?_ ?_
  · rw [Matrix.map_mul, archMatFun_map_arch, finMatFun_map_arch, Matrix.one_mul]; ext i j; rfl
  · rw [Matrix.map_mul, archMatFun_map_fin, finMatFun_map_fin, Matrix.mul_one]; ext i j; rfl

private def finLift : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin 2) (AdeleRing (𝓞 F) F) :=
  Units.map (finMat F)

private def archLift : GL (Fin 2) (InfiniteAdeleRing F) →* GL (Fin 2) (AdeleRing (𝓞 F) F) :=
  Units.map (archMat F)

private theorem glFin_finLift (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (finLift F m) = m := by
  ext i j : 2
  rfl

private theorem glArch_finLift (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (finLift F m) = 1 := by
  ext i j : 2
  rfl

private theorem glArch_archLift (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch (𝓞 F) F (archLift F a) = a := by
  ext i j : 2
  rfl

private theorem glFin_archLift (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin (𝓞 F) F (archLift F a) = 1 := by
  ext i j : 2
  rfl

private theorem archLift_mul_finLift (y : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    archLift F (glArch (𝓞 F) F y) * finLift F (glFin (𝓞 F) F y) = y := by
  refine Units.ext ?_
  show archMatFun F _ * finMatFun F _ = _
  rw [archMatFun_mul_finMatFun]
  rfl

private theorem archLift_mul_finLift_comm (a : GL (Fin 2) (InfiniteAdeleRing F))
    (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    archLift F a * finLift F m = finLift F m * archLift F a := by
  refine Units.ext ?_
  show archMatFun F _ * finMatFun F _ = finMatFun F _ * archMatFun F _
  rw [archMatFun_mul_finMatFun, finMatFun_mul_archMatFun]

private theorem finLift_mem_finiteAdelicGL2Subgroup (m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finLift F m ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact glArch_finLift F m

private theorem finLift_mem_levelOne_inf {N : Ideal (𝓞 F)} {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteLevelOne (𝓞 F) F N) :
    finLift F k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine ⟨?_, finLift_mem_finiteAdelicGL2Subgroup F k⟩
  show glFin (𝓞 F) F (finLift F k) ∈ finiteLevelOne (𝓞 F) F N
  rwa [glFin_finLift]

private theorem image_glFin_levelOne_inf (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (GL (Fin 2) (AdeleRing (𝓞 F) F)))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.1
  · intro hm
    exact ⟨finLift F m, finLift_mem_levelOne_inf F hm, glFin_finLift F m⟩

theorem isFinTestFactor_indicator_levelOne (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsFinTestFactor F (Set.indicator ((glFin (𝓞 F) F) ''
      (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (GL (Fin 2) (AdeleRing (𝓞 F) F))))
      (fun _ => (1 : ℂ))) := by
  classical
  rw [image_glFin_levelOne_inf F N]
  set Kf : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := finiteLevelOne (𝓞 F) F N with hKf
  have hKopen : IsOpen (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isOpen_finiteLevelOne (𝓞 F) F hN
  have hKcomp : IsCompact (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isCompact_finiteLevelOne (𝓞 F) F N
  have hKclosed : IsClosed (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isClosed_finiteLevelOne (𝓞 F) F N
  have hind_lc : IsLocallyConstant ((Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    · exact ⟨Kf, hKopen, hx, fun b hb => by rw [Set.indicator_of_mem hb, Set.indicator_of_mem hx]⟩
    · exact ⟨(Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))ᶜ, hKclosed.isOpen_compl, hx, fun b hb => by
        rw [Set.indicator_of_notMem (Set.notMem_of_mem_compl hb), Set.indicator_of_notMem hx]⟩
  have hind_cs : HasCompactSupport ((Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hKcomp fun b hb => Set.indicator_of_notMem hb _
  exact ⟨hind_lc, hind_cs⟩

end R5cGlue.LevelAux
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue.LevelAux"
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue"

namespace R5cGlue

variable (F : Type) [Field F] [NumberField F]

theorem isFactorizableTestFn_of_isLevelSphericalOfType (tys : ArchTypeFamily F) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f) :
    IsFactorizableTestFn F f := by
  obtain ⟨fa, hfa, -, -, hf⟩ := hf
  exact ⟨fa, _, hfa, LevelAux.isFinTestFactor_indicator_levelOne F N hN, hf⟩

end R5cGlue
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue.LevelAux"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue.LevelAux"

namespace R5cGlue

noncomputable abbrev pins (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    CarrierPins F :=
  productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

end R5cGlue
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.R5cGlue.LevelAux"

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hreal : ∀ w : InfinitePlace F, w.IsReal)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hfin : FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ)))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)) :
    ∃ lam : ℂ, ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ), rightConv F φ f = lam • φ := by
  classical

  by_cases hbot : (V ⊓ levelInvariantSubmodule F (R5cGlue.pins F c u d₁ d₂ T) N ⊓
      archCutSubmodule F (ArchTypeFamily.ofChar F χ)) = ⊥
  · refine ⟨0, fun φ hφ => ?_⟩
    have hφ0 : φ = 0 := by
      have : φ ∈ (V ⊓ levelInvariantSubmodule F (R5cGlue.pins F c u d₁ d₂ T) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ)) := hφ
      rw [hbot] at this; exact (Submodule.mem_bot ℂ).mp this
    subst hφ0; rw [zero_smul]; exact rightConv_zero_left F f

  obtain ⟨φ₀, hφ₀X, hφ₀ne⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hcont : ∀ φ ∈ V, Continuous φ := by
    intro φ hφ
    have hmem := hV.1.le hφ
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hmem
    · rintro φ ⟨-, hc', -⟩; exact hc'
    · exact continuous_const
    · intro a b _ _ ha hb; exact ha.add hb
    · intro a b _ hb; exact hb.const_smul a
  have hχ1 := AutomorphicForm.norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar F χ φ₀ (hcont φ₀ hφ₀X.1.1) hφ₀ne hφ₀X.2

  obtain ⟨σ, hσ⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V hV
  have hirr : ∀ w, (ArchRepAt.ofChar F (χ w)).ρ.IsIrreducible := fun w => R5cGlue.isIrreducible_ofChar F (χ w)

  have hsphL : IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ) ((R5cGlue.pins F c u d₁ d₂ T).U N) f := hsph

  have key : ∀ g : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F g →
      IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ) ((R5cGlue.pins F c u d₁ d₂ T).U N) g → flat F σ g = g →
      ∃ lam : ℝ, ∀ φ ∈ V ⊓ levelInvariantSubmodule F (R5cGlue.pins F c u d₁ d₂ T) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ), rightConv F φ g = (lam : ℂ) • φ := by
    intro g hgT hgs hgflat
    exact AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType F
      c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ N hN (fun w => ArchRepAt.ofChar F (χ w)) hirr V hV g hgT hgs hgflat

  have hf'S : IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ) ((R5cGlue.pins F c u d₁ d₂ T).U N) (flat F σ f) :=
    AutomorphicForm.isLevelSphericalOfType_ofChar_flat F σ χ hχ1 N f hsphL

  have hcomb : ∀ a b : ℂ, IsFactorizableTestFn F (a • f + b • flat F σ f) ∧
      IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ) ((R5cGlue.pins F c u d₁ d₂ T).U N)
        (a • f + b • flat F σ f) := by
    intro a b
    have hs := R5cGlue.isLevelSphericalOfType_add_smul F _ _ f _ a b hsphL hf'S
    exact ⟨R5cGlue.isFactorizableTestFn_of_isLevelSphericalOfType F _ N hN _ hs, hs⟩
  have hflat₁ : flat F σ ((1/2 : ℂ) • f + (1/2 : ℂ) • flat F σ f) = (1/2 : ℂ) • f + (1/2 : ℂ) • flat F σ f := by
    rw [R5cGlue.flat_add_smul, R5cGlue.flat_flat]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_div₀, map_one, map_ofNat]
    ring
  have hflat₂ : flat F σ ((-Complex.I/2) • f + (Complex.I/2) • flat F σ f) =
      (-Complex.I/2) • f + (Complex.I/2) • flat F σ f := by
    rw [R5cGlue.flat_add_smul, R5cGlue.flat_flat]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring
  obtain ⟨lam₁, h₁⟩ := key _ (hcomb _ _).1 (hcomb _ _).2 hflat₁
  obtain ⟨lam₂, h₂⟩ := key _ (hcomb _ _).1 (hcomb _ _).2 hflat₂
  refine ⟨(lam₁ : ℂ) + Complex.I * (lam₂ : ℂ), fun φ hφ => ?_⟩
  obtain ⟨h1c, h1cs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ (hcomb (1/2) (1/2)).1
  obtain ⟨h2c, h2cs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (hcomb (-Complex.I/2) (Complex.I/2)).1
  have hdecomp : f = (1 : ℂ) • ((1/2 : ℂ) • f + (1/2 : ℂ) • flat F σ f) +
      Complex.I • ((-Complex.I/2) • f + (Complex.I/2) • flat F σ f) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((f x) / 2 - (flat F σ f x) / 2) * Complex.I_mul_I
  rw [hdecomp, R5cGlue.rightConv_add_smul_right F (hcont φ hφ.1.1) h1c h1cs h2c h2cs, h₁ φ hφ, h₂ φ hφ,
    one_smul, smul_smul, ← add_smul]

end S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos (solution)
