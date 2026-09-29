-- Prove2me | solution 1 for AutomorphicForm.exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fa61b467-71e4-5c5c-b1c9-d42910696237

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_AdelicTraceProducer
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome"
p2m_attr_erase "simp" "LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open NumberField.AdelicVolume
open scoped Real

namespace P2M
namespace IsotypicSmooth

section CoefficientKit

variable (F : Type) [Field F] [NumberField F]

section RealUnipotent

private theorem archRealGLAt_unipotentGL2_eq {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ∃ X : InfiniteAdeleRing F, X w = (ringEquivRealOfIsReal hw).symm x ∧ (∀ v : InfinitePlace F, v ≠ w → X v = 0) ∧
      archRealGLAt hw (unipotentGL2 x) = unipotentGL2 ((⟨X, 0⟩ : AdeleRing (𝓞 F) F)) := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (unipotentGL2 x) with hm
  refine ⟨archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1, ?_, ?_, ?_⟩
  · rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
    simp [unipotentGL2_coe]
  · intro v hv
    rw [archMatrixUpdate_apply_of_ne F w _ 0 1 hv]
    simp [Matrix.one_apply]
  · refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
    · have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = archGLIncl F w m :=
        glArch_adelicArchGLIncl F _
      rw [h1]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glArch_apply]
      change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
      funext v
      by_cases hv : v = w
      · subst hv
        rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry] <;> rfl
      · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, Matrix.one_apply,
            archMatrixUpdate_apply_of_ne F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 hv] <;> rfl
    · have h2 : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = 1 := glFin_adelicArchGLIncl F _
      rw [h2]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glFin_apply]
      fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe, Matrix.one_apply]

private theorem apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {w : InfinitePlace F} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing F, (∀ w' : InfinitePlace F, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 F) F) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ (X : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 X * g) = ψ X * W g)
    (x : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g := by
  obtain ⟨X, hXw, hX0, hX⟩ := archRealGLAt_unipotentGL2_eq F hw x
  rw [hX]
  refine (hW ⟨X, 0⟩ g).trans ?_
  rw [hψr X hX0, hXw]
  congr 3
  rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]

end RealUnipotent
section Periodicity

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((unipotentGL2 β : Matrix (Fin 2) (Fin 2) F) i j)
    = (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

variable {F}

private theorem isLsXiFunction_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) : IsLsXiFunction (𝓞 F) F pins.Z ξ φ := by
  letI := pins.mS
  exact ((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp h.smoothCusp.1.1).1

private theorem apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ)
    (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  have hinv := (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hinv]

end Periodicity

section ReferenceDatum

variable {F}

private theorem apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  rw [← globalPoints_unipotentGL2, (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant]

private theorem whittakerCoefficient_zero_of_isIsotypicCuspFormAt
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g = 0 := by
  rw [whittakerCoefficient_zero_eq_constantTerm]
  exact h.smoothCusp.1.2 g

end ReferenceDatum
section ReferenceDatumRat

private theorem glArch_archRealGLAt_archRealProjAt_rat {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = AdelicLevel.glArch (𝓞 ℚ) ℚ g := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw g) with hm
  have h1 : AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = archGLIncl ℚ w m :=
    glArch_adelicArchGLIncl ℚ _
  rw [h1]
  apply Units.ext
  ext i j
  change archMatrixUpdate ℚ w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
  funext v
  rw [Subsingleton.elim v w, archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
  change (ringEquivRealOfIsReal hw).symm ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (AdelicLevel.archComponent ℚ w (AdelicLevel.glArch (𝓞 ℚ) ℚ g)) : Matrix (Fin 2) (Fin 2) ℝ) i j) = _
  rw [glEquivOfRingEquiv_apply_entry, RingEquiv.symm_apply_apply, AdelicLevel.archComponent_apply]

private theorem glArch_inv_archRealGLAt_archRealProjAt_mul_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, glArch_archRealGLAt_archRealProjAt_rat, inv_mul_cancel]

open NumberField.StandardAddChar in

private theorem unipotentGL2_ratArchLine_eq_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (t : ℝ) :
    unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) = archRealGLAt hw (unipotentGL2 t) := by
  obtain ⟨X, hXw, -, hX⟩ := archRealGLAt_unipotentGL2_eq ℚ hw t
  rw [hX]
  congr 2
  funext v
  rw [Subsingleton.elim v w, hXw]
  rfl

private theorem det_of_entries_ne_zero (m : GL (Fin 2) ℝ) :
    (Matrix.of fun i j => (m : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin 2) (Fin 2) ℝ)).mp m.isUnit |>.ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw fun i j => (m : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [archRealLiftAt_of_det_ne_zero hw (det_of_entries_ne_zero m)]
  congr 1
  exact Units.ext rfl

private theorem contDiff_unipotent_entries :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> first | exact contDiff_const | exact contDiff_id

private theorem exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (p : GL (Fin 2) ℝ) (k : AdelicGL2 (𝓞 ℚ) ℚ), AdelicLevel.glArch (𝓞 ℚ) ℚ k = 1 ∧ g = archRealGLAt hw p * k :=
  ⟨archRealProjAt hw g, _, glArch_inv_archRealGLAt_archRealProjAt_mul_rat hw g, (mul_inv_cancel_left _ _).symm⟩

open NumberField.StandardAddChar in

private theorem contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ 2 fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g) := by
  obtain ⟨p, k, hkarch, hg⟩ := exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat hw g
  have hfun : (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g))
      = (fun e : Fin 2 → Fin 2 → ℝ => φ (k * (1 * archRealLiftAt hw e))) ∘
          (fun t : ℝ => (Matrix.of.symm
            (Matrix.of (fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
              * (p : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ)) := by
    funext t
    simp only [Function.comp, one_mul]
    rw [unipotentGL2_ratArchLine_eq_archRealGLAt hw t, hg, ← mul_assoc, ← map_mul,
      archRealGLAt_mul_comm_of_glArch_eq_one hw _ hkarch, archRealGLAt_eq_archRealLiftAt]
    rfl
  rw [hfun]
  have hcurve : ∀ t : ℝ, (Matrix.of (Matrix.of.symm
      (Matrix.of (fun i j => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        * (p : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    intro t
    rw [Equiv.apply_symm_apply]
    exact det_of_entries_ne_zero (unipotentGL2 t * p)
  exact (ContDiffOn.comp_contDiff (hφ.comp_mul_left k 1)
    ((contDiff_of_symm_mul_const _).comp contDiff_unipotent_entries) hcurve).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hsm : IsArchSmoothAt hw φ) (hne : φ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hne
  have hsum := (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ φ
    (fun β g => (apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt hiso) β g) hiso.smoothCusp.2
    (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw hsm g)).2 g₀
  exact exists_whittakerCoefficient_one_ne_zero ℚ D U gen ψ hψ φ
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso).left_invariant g₀
    ((whittakerCoefficient_zero_of_isIsotypicCuspFormAt hiso) ψ g₀)
    (hiso.continuous.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)).mul continuous_const)) hsum hg₀

end ReferenceDatumRat

private theorem isKfSmooth_of_exists_rightConv_eq
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hconv : ∃ α : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α ∧ rightConv F φ α = φ) :
    IsKfSmooth F φ := by
  obtain ⟨α, hα, hαφ⟩ := hconv
  have h := isKfSmooth_rightConv F φ α hα
  rwa [hαφ] at h

end CoefficientKit

section PolynomialGrowthOfCoefficients

section CharChange

variable (F : Type) [Field F] [NumberField F]

private theorem whittakerCoefficient_one_eq_whittakerCoefficient_of_forall_eq_mul (pins : CarrierPins F)
    (ψ ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a : F)
    (hψ : ∀ x : AdeleRing (𝓞 F) F, ψ x = ψ₀ (algebraMap F (AdeleRing (𝓞 F) F) a * x))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 1 g = whittakerCoefficient F pins ψ₀ φ a g := by
  unfold whittakerCoefficient
  simp only [hψ, map_one, one_mul, mul_neg]

end CharChange

section Translate

variable (F : Type) [Field F] [NumberField F]

private theorem whittakerCoefficient_fun_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun h => φ (h * t)) α g = whittakerCoefficient F pins ψ φ α (g * t) := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

variable {F}

private theorem exists_isFactorizableTestFn_rightConv_eq_fun_mul {φ α : AdelicGL2 (𝓞 F) F → ℂ}
    (hα : IsFactorizableTestFn F α) (hφ : rightConv F φ α = φ) (t : AdelicGL2 (𝓞 F) F) :
    ∃ α' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α' ∧ rightConv F φ α' = fun h => φ (h * t) := by
  refine ⟨fun y => α (t⁻¹ * y), isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F α hα t, ?_⟩
  funext h
  rw [← rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ α h t, hφ]

end Translate
section ArchCutTranslate

variable (F : Type) [Field F] [NumberField F]

private theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup {t : AdelicGL2 (𝓞 F) F}
    (ht : t ∈ finiteAdelicGL2Subgroup F) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute t (rowIsometryInclAt₀ F w k) := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at ht
  show t * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * t
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, ht, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀ F w k, one_mul, mul_one]

private theorem comp_mul_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) {t : AdelicGL2 (𝓞 F) F}
    (ht : t ∈ finiteAdelicGL2Subgroup F) :
    (fun x => f (x * t)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * t)) ∈
      ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i
      (comp_mul_mem_typeSubmodule_of_commute hfi t fun k =>
        commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup F ht w k)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

end ArchCutTranslate

section IndexShift

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar in

private theorem setIntegral_adelicBox_unipotent_globalPoints_mul_eq [Countable F]
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : ∀ u : AdeleRing (𝓞 F) F,
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F γ
        = globalPoints (𝓞 F) F γ * unipotentGL2 u)
    (h : AdelicGL2 (𝓞 F) F) :
    (letI := adeleBorel (𝓞 F) F
      ∫ x in adelicBox F, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x) ∂adelicAddHaar (𝓞 F) F)
      = (letI := adeleBorel (𝓞 F) F
        ∫ u in adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(algebraMap F (AdeleRing (𝓞 F) F) a * u))
          ∂adelicAddHaar (𝓞 F) F) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  set A : AdeleRing (𝓞 F) F := algebraMap F (AdeleRing (𝓞 F) F) a with hA
  have hcont : ∀ c : AdeleRing (𝓞 F) F, Measurable fun x : AdeleRing (𝓞 F) F => c * x :=
    fun c => (continuous_const.mul continuous_id).measurable
  let e : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F :=
    { toFun := fun x => A * x
      invFun := fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x
      left_inv := fun x => by
        show algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * (algebraMap F (AdeleRing (𝓞 F) F) a * x) = x
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
      right_inv := fun x => by
        show algebraMap F (AdeleRing (𝓞 F) F) a * (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) = x
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
      measurable_toFun := hcont A
      measurable_invFun := hcont _ }
  have hmp : MeasurePreserving e (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F) :=
    measurePreserving_mul_algebraMap_adelicAddHaar F a ha
  have hpre : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (e ⁻¹' adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F (adelicAddHaar (𝓞 F) F) a ha
  have hbox : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    isAddFundamentalDomain_adelicBox_adelicAddHaar F

  have hF₂ : ∀ (b : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (b +ᵥ u) * h) * ψ₀ (-(A * (b +ᵥ u))) = φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) := by
    rintro ⟨_, b, rfl⟩ u
    show φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * h)
        * ψ₀ (-(A * (algebraMap F (AdeleRing (𝓞 F) F) b + u))) = φ (unipotentGL2 u * h) * ψ₀ (-(A * u))
    rw [hper b u h, mul_add, neg_add, hA, ← map_mul, ← map_neg, AddChar.map_add_eq_mul, hψ₀, one_mul]

  have hGe : ∀ u : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 (e u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(e u))
        = φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) := by
    intro u
    show φ (unipotentGL2 (A * u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(A * u))
        = φ (unipotentGL2 u * h) * ψ₀ (-(A * u))
    rw [show unipotentGL2 (A * u) * (globalPoints (𝓞 F) F γ * h) = globalPoints (𝓞 F) F γ * (unipotentGL2 u * h) by
      rw [← mul_assoc, hγ u, mul_assoc], hinv γ]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
    (Set.countable_range (algebraMap F (AdeleRing (𝓞 F) F))).to_subtype
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) (adelicAddHaar (𝓞 F) F) :=
    ⟨fun c s _ => measure_preimage_add _ (c : AdeleRing (𝓞 F) F) s⟩
  calc (∫ x in adelicBox F, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x) ∂adelicAddHaar (𝓞 F) F)
      = ∫ u in e ⁻¹' adelicBox F,
          φ (unipotentGL2 (e u) * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-(e u)) ∂adelicAddHaar (𝓞 F) F :=
        (hmp.setIntegral_preimage_emb e.measurableEmbedding
          (fun x => φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x)) (adelicBox F)).symm
    _ = ∫ u in e ⁻¹' adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) ∂adelicAddHaar (𝓞 F) F := by
        simp only [hGe]
    _ = ∫ u in adelicBox F, φ (unipotentGL2 u * h) * ψ₀ (-(A * u)) ∂adelicAddHaar (𝓞 F) F :=
        hpre.setIntegral_eq hbox (f := fun u => φ (unipotentGL2 u * h) * ψ₀ (-(A * u))) hF₂

private theorem whittakerCoefficient_one_globalPoints_mul_eq_whittakerCoefficient [Countable F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : ∀ u : AdeleRing (𝓞 F) F,
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F γ
        = globalPoints (𝓞 F) F γ * unipotentGL2 u)
    (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ 1 (globalPoints (𝓞 F) F γ * h)
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ a h := by
  have key := setIntegral_adelicBox_unipotent_globalPoints_mul_eq F ψ₀ hψ₀ φ hinv hper a ha γ hγ h
  unfold whittakerCoefficient
  simp only [map_one, one_mul]
  change (∫ x, φ (unipotentGL2 x * (globalPoints (𝓞 F) F γ * h)) * ψ₀ (-x)
      ∂((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • (adelicAddHaar (𝓞 F) F).restrict (adelicBox F))
    = ∫ x, φ (unipotentGL2 x * h) * ψ₀ (-(algebraMap F (AdeleRing (𝓞 F) F) a * x))
      ∂((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • (adelicAddHaar (𝓞 F) F).restrict (adelicBox F)
  rw [integral_smul_measure, integral_smul_measure, key]

private noncomputable def diagOneGlobal (a : F) (ha : a ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by simp [ha])

private theorem globalPoints_diagOneGlobal_coe (a : F) (ha : a ≠ 0) :
    ((globalPoints (𝓞 F) F (diagOneGlobal F a ha) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![algebraMap F (AdeleRing (𝓞 F) F) a, 0; 0, 1] := by
  ext i j
  rw [globalPoints_apply]
  change algebraMap F (AdeleRing (𝓞 F) F) ((!![a, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j) = _
  fin_cases i <;> fin_cases j <;> simp

private theorem unipotentGL2_mul_globalPoints_diagOneGlobal (a : F) (ha : a ≠ 0) (u : AdeleRing (𝓞 F) F) :
    unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) * globalPoints (𝓞 F) F (diagOneGlobal F a ha)
      = globalPoints (𝓞 F) F (diagOneGlobal F a ha) * unipotentGL2 u := by
  apply Units.ext
  show (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) a * u) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * (globalPoints (𝓞 F) F (diagOneGlobal F a ha) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (globalPoints (𝓞 F) F (diagOneGlobal F a ha) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * (unipotentGL2 u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  rw [globalPoints_diagOneGlobal_coe, unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem whittakerCoefficient_eq_whittakerCoefficient_one_diagOneGlobal_mul [Countable F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ₀ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ₀ : IsPrincipalInvariantAddChar F ψ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hper : ∀ (b : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) b + u) * g) = φ (unipotentGL2 u * g))
    (a : F) (ha : a ≠ 0) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ a h
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ₀ φ 1
          (globalPoints (𝓞 F) F (diagOneGlobal F a ha) * h) :=
  (whittakerCoefficient_one_globalPoints_mul_eq_whittakerCoefficient F D U gen ψ₀ hψ₀ φ hinv hper a ha _
    (unipotentGL2_mul_globalPoints_diagOneGlobal F a ha) h).symm

end IndexShift
section Growth

private noncomputable def archInclHom : InfiniteAdeleRing ℚ →* AdeleRing (𝓞 ℚ) ℚ where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

private noncomputable def archIdele (a : ℚ) (ha : a ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map archInclHom (Units.map (algebraMap ℚ (InfiniteAdeleRing ℚ)).toMonoidHom (Units.mk0 a ha))

private noncomputable def finIdele (a : ℚ) (ha : a ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ)
    (Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha))

private theorem archIdele_coe_snd
    (a : ℚ) (ha : a ≠ 0) : ((archIdele a ha : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 :=
  rfl

private theorem finIdele_coe_fst
    (a : ℚ) (ha : a ≠ 0) : ((finIdele a ha : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
  rfl

private theorem principal_eq_archIdele_mul_finIdele (a : ℚ) (ha : a ≠ 0) :
    Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha) = archIdele a ha * finIdele a ha := by
  apply Units.ext
  apply Prod.ext
  · show algebraMap ℚ (InfiniteAdeleRing ℚ) a = algebraMap ℚ (InfiniteAdeleRing ℚ) a * 1
    rw [mul_one]
  · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a = 1 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a
    rw [one_mul]

private theorem globalPoints_diagOneGlobal_eq_diagOne (a : ℚ) (ha : a ≠ 0) :
    globalPoints (𝓞 ℚ) ℚ (diagOneGlobal ℚ a ha)
      = diagOne (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Units.mk0 a ha)) := by
  apply Units.ext
  rw [globalPoints_diagOneGlobal_coe]
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_finIdele_mem (a : ℚ) (ha : a ≠ 0) : diagOne (finIdele a ha) ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  apply Units.ext
  ext i j
  rw [glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [finIdele_coe_fst] <;> rfl

private theorem exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ}
    {φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ N S Φ φ₁)
    (hne : φ₁ ≠ 0)
    {α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hα : IsFactorizableTestFn ℚ α) (hconv : rightConv ℚ φ₁ α = φ₁)
    {tys : ArchTypeFamily ℚ} (hk : φ₁ ∈ archCutSubmodule ℚ tys)
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) {t : AdelicGL2 (𝓞 ℚ) ℚ} (ht : t ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
      ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ)) ψ φ₁ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M := by

  obtain ⟨a₀, ha₀, hψa₀⟩ := exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar ℚ hψ
  have hstd : IsPrincipalInvariantAddChar ℚ (StandardAddChar.stdAddChar ℚ) :=
    (StandardAddChar.isGlobalAddChar_stdAddChar ℚ).principalInvariant

  have hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ₁ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ₁ g :=
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso).left_invariant
  have hper : ∀ (b : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ₁ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) b + x) * g) = φ₁ (unipotentGL2 x * g) :=
    fun b x g => (apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt hiso) b x g

  obtain ⟨hcls, hcts⟩ := isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous ℚ ξ φ₁
    (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hiso.continuous (Function.ne_iff.mp hne)
  let e : (AdeleRing (𝓞 ℚ) ℚ)ˣ ≃* (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) := Subgroup.topEquiv.symm
  have hcls' : IsIdeleClassChar (𝓞 ℚ) ℚ (ξ.comp e.toMonoidHom) := fun v => hcls v
  obtain ⟨w₀, hw₀⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow ℚ (ξ.comp e.toMonoidHom) hcls' hcts

  have hfin : diagOne (finIdele a₀ ha₀) * t ∈ finiteAdelicGL2Subgroup ℚ :=
    (finiteAdelicGL2Subgroup ℚ).mul_mem (diagOne_finIdele_mem a₀ ha₀) ht
  obtain ⟨α', hα', hα'eq⟩ := exists_isFactorizableTestFn_rightConv_eq_fun_mul hα hconv (diagOne (finIdele a₀ ha₀) * t)
  have hxt : rightConv ℚ φ₁ α' ∈ archCutSubmodule ℚ tys := by
    rw [hα'eq]
    exact comp_mul_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup ℚ hk hfin

  obtain ⟨C, hC⟩ :=
    exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
      ℚ c u d₁ d₂ T hd hcov ξ φ₁ hiso.smoothCusp.1 hiso.continuous α' hα' tys hxt w₀
    (fun z => hw₀ z) 0
  refine ⟨C * ideleNorm ℚ (archIdele a₀ ha₀) ^ (w₀ / 2), w₀ / 2, fun a ha => ?_⟩

  have hdatum : globalPoints (𝓞 ℚ) ℚ (diagOneGlobal ℚ a₀ ha₀) * (diagOne a * t)
      = diagOne (archIdele a₀ ha₀ * a) * (diagOne (finIdele a₀ ha₀) * t) := by
    rw [globalPoints_diagOneGlobal_eq_diagOne, principal_eq_archIdele_mul_finIdele, map_mul, map_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← map_mul, mul_comm (finIdele a₀ ha₀) a, map_mul, mul_assoc]
  have hsnd : ((archIdele a₀ ha₀ * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    rw [Units.val_mul]
    show ((archIdele a₀ ha₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2
        * ((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1
    rw [archIdele_coe_snd, ha, one_mul]
  have hb := hC 1 (map_one _) (fun _ => by rw [map_one, map_one]; exact isRowIsometry_one)
    (archIdele a₀ ha₀ * a) hsnd w
  rw [mul_one, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, ideleNorm_mul,
    Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, ← mul_assoc] at hb
  rw [whittakerCoefficient_one_eq_whittakerCoefficient_of_forall_eq_mul ℚ _ ψ (StandardAddChar.stdAddChar ℚ) a₀ hψa₀,
    whittakerCoefficient_eq_whittakerCoefficient_one_diagOneGlobal_mul ℚ _ _ _ (StandardAddChar.stdAddChar ℚ) hstd φ₁
      hinv hper a₀ ha₀, hdatum, ← whittakerCoefficient_fun_mul, ← hα'eq]
  exact hb

end Growth

end PolynomialGrowthOfCoefficients

section IsotypicReproduction

open NumberField IsDedekindDomain NumberField.AdelicLevel

noncomputable section

variable {F : Type} [Field F] [NumberField F]

private def realizationOfIsIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {S : Finset
    (HeightOneSpectrum (𝓞 F))}
    {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) : SmoothCuspRealizationAt F pins Φ.toRawCentral where
  toFun := φ
  exists_ne_zero := by
    obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
    exact ⟨g, hg⟩
  centralChar := ξ
  smoothCusp := hφ.smoothCusp
  level_invariant := hφ.level_invariant
  exceptionalSet := S
  hecke_eigen := hφ.hecke_eigen
  central_eigen := hφ.central_eigen

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_toFun {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).toFun = φ := rfl

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_centralChar {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).centralChar = ξ := rfl

@[scoped simp] private theorem realizationOfIsIsotypicCuspFormAt_exceptionalSet {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F pins ξ Φ.level S Φ φ) (hne : φ ≠ 0) :
    (realizationOfIsIsotypicCuspFormAt hφ hne).exceptionalSet = S := rfl

open scoped Classical in
private theorem isArchTestFactor_add {fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h₁ : IsArchTestFactor F fa₁)
    (h₂ : IsArchTestFactor F fa₂) : IsArchTestFactor F (fa₁ + fa₂) := by
  obtain ⟨⟨Φ₁, hΦ₁, hfa₁⟩, hc₁⟩ := h₁
  obtain ⟨⟨Φ₂, hΦ₂, hfa₂⟩, hc₂⟩ := h₂
  refine ⟨⟨Φ₁ + Φ₂, hΦ₁.add hΦ₂, fun g => ?_⟩, hc₁.add hc₂⟩
  simp only [Pi.add_apply, hfa₁ g, hfa₂ g]

open scoped Classical in
private theorem isArchTestFactor_smul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  refine ⟨⟨c • Φ, hΦ.const_smul c, fun g => ?_⟩, hc.mono fun g hg => ?_⟩
  · simp only [Pi.smul_apply, hfa g]
  · intro h0
    exact hg (by simp only [Pi.smul_apply, h0, smul_zero])

private def tensorTestFn (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ :=
  fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)

private theorem tensorTestFn_apply (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing
    (𝓞 F) F) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : tensorTestFn fa ff g = fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := rfl

private theorem isFactorizableTestFn_tensorTestFn {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (tensorTestFn fa ff) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

private theorem isFactorizableTestFn_exists_eq_tensorTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧ f = tensorTestFn fa ff := by
  obtain ⟨fa, ff, hfa, hff, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, funext hf⟩

private theorem tensorTestFn_add_smul (fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (c : ℂ) :
    tensorTestFn fa₁ ff + c • tensorTestFn fa₂ ff = tensorTestFn (fa₁ + c • fa₂) ff := by
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, tensorTestFn_apply, smul_eq_mul]
  ring

private theorem tensorTestFn_support_of_forall {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} {G : Subgroup (GL (Fin 2) (AdeleRing (𝓞 F) F))}
    (hff : ∀ x : GL (Fin 2) (AdeleRing (𝓞 F) F), ff (glFin (𝓞 F) F x) ≠ 0 →
      ∃ a k : GL (Fin 2) (AdeleRing (𝓞 F) F), glFin (𝓞 F) F a = 1 ∧ k ∈ G ∧ x = a * k) :
    ∀ x : GL (Fin 2) (AdeleRing (𝓞 F) F), tensorTestFn fa ff x ≠ 0 →
      ∃ a k : GL (Fin 2) (AdeleRing (𝓞 F) F), glFin (𝓞 F) F a = 1 ∧ k ∈ G ∧ x = a * k :=
  fun x hx => hff x (right_ne_zero_of_mul hx)

private theorem tensorTestFn_add (fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tensorTestFn (fa₁ + fa₂) ff = tensorTestFn fa₁ ff + tensorTestFn fa₂ ff := by
  funext g
  simp only [Pi.add_apply, tensorTestFn_apply, add_mul]

private theorem tensorTestFn_comp_inv_mul_of_glFin_eq_one (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) {t : GL (Fin 2) (AdeleRing (𝓞 F) F)} (ht : glFin (𝓞 F) F t = 1) :
    (fun y => tensorTestFn fa ff (t⁻¹ * y)) = tensorTestFn (fun x => fa ((glArch (𝓞 F) F t)⁻¹ * x)) ff := by
  funext y
  simp only [tensorTestFn_apply, map_mul, map_inv, ht, inv_one, one_mul]

private theorem tensorTestFn_comp_inv_mul_adelicArchGLIncl (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    (fun y => tensorTestFn fa ff ((adelicArchGLIncl F k)⁻¹ * y)) = tensorTestFn (fun x => fa (k⁻¹ * x)) ff := by
  funext y
  simp only [tensorTestFn_apply, map_mul, map_inv, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, inv_one, one_mul]

private def entryMulLeft (a : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) where
  toFun e := fun i j => ∑ k, a i k * e k j
  map_add' e₁ e₂ := by
    funext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r e := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

omit [NumberField F] in
private theorem archEntries_mul (m g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (m * g) = entryMulLeft (archEntries F m) (archEntries F g) := by
  funext i j
  simp only [archEntries_apply, entryMulLeft, LinearMap.coe_mk, AddHom.coe_mk, Units.val_mul, Matrix.mul_apply,
    map_sum, map_mul]

open scoped Classical in

private theorem isArchTestFactor_comp_mul_left {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa)
    (m : GL (Fin 2) (InfiniteAdeleRing F)) : IsArchTestFactor F (fun x => fa (m * x)) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  refine ⟨⟨Φ ∘ LinearMap.toContinuousLinearMap (entryMulLeft (archEntries F m)),
    hΦ.comp (LinearMap.toContinuousLinearMap (entryMulLeft (archEntries F m))).contDiff, fun g => ?_⟩, ?_⟩
  · exact (hfa (m * g)).trans (congrArg Φ (archEntries_mul m g))
  · exact hc.comp_homeomorph (Homeomorph.mulLeft m)

private theorem isFactorizableTestFn_comp_inv_mul_adelicArchGLIncl_tensorTestFn {fa : GL (Fin 2)
    (InfiniteAdeleRing F) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff)
    (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    IsFactorizableTestFn F (fun y => tensorTestFn fa ff ((adelicArchGLIncl F k)⁻¹ * y)) := by
  rw [tensorTestFn_comp_inv_mul_adelicArchGLIncl]
  exact isFactorizableTestFn_tensorTestFn ((isArchTestFactor_comp_mul_left hfa) k⁻¹) hff

private theorem tensorTestFn_smul (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : tensorTestFn (c • fa) ff = c • tensorTestFn fa ff := by
  funext g
  simp only [tensorTestFn_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem tensorTestFn_finset_sum_smul {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tensorTestFn (∑ i ∈ s, c i • fa i) ff = ∑ i ∈ s, c i • tensorTestFn (fa i) ff := by
  funext g
  simp only [tensorTestFn_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

private theorem isArchTestFactor_finset_sum {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : ∀ i, IsArchTestFactor F (fa i)) :
    IsArchTestFactor F (∑ i ∈ s, c i • fa i) :=
  Finset.sum_induction (fun i => c i • fa i) (IsArchTestFactor F) (fun _ _ ha hb => (isArchTestFactor_add ha) hb)
    (isArchTestFactor_zero F) fun i _ => (isArchTestFactor_smul (hfa i)) (c i)

private theorem rightConv_const_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (fun y => c * f y) = c • rightConv F φ f := by
  funext g
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, MeasureTheory.integral_const_mul]

private theorem rightConv_smul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (c • f) = c • rightConv F φ f :=
  rightConv_const_mul_right φ c f

private theorem rightConv_add_right {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁) (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) :
    rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ {f : AdelicGL2 (𝓞 F) F → ℂ}, Continuous f → HasCompactSupport f → ∀ g : AdelicGL2 (𝓞 F) F,
      MeasureTheory.Integrable (fun x => φ (g * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro f hf hfc g
    exact ((hφ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfc.mul_left
  funext g
  simp only [rightConv_apply, Pi.add_apply, mul_add]
  exact MeasureTheory.integral_add (hint h₁ h₁c g) (hint h₂ h₂c g)

private theorem rightConv_zero_right' (φ : AdelicGL2 (𝓞 F) F → ℂ) : rightConv F φ 0 = 0 := by
  funext g
  simp [rightConv_apply]

private theorem rightConv_finset_sum_right {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {ι : Type} (s : Finset ι)
    {h : ι → AdelicGL2 (𝓞 F) F → ℂ} (hh : ∀ i ∈ s, Continuous (h i) ∧ HasCompactSupport (h i)) :
    rightConv F φ (∑ i ∈ s, h i) = ∑ i ∈ s, rightConv F φ (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, rightConv_zero_right']
  | insert a s has ih =>
    have hs : Continuous (∑ i ∈ s, h i) ∧ HasCompactSupport (∑ i ∈ s, h i) :=
      Finset.sum_induction h (fun f => Continuous f ∧ HasCompactSupport f)
        (fun _ _ ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩) ⟨continuous_zero, HasCompactSupport.zero⟩
        fun i hi => hh i (Finset.mem_insert_of_mem hi)
    have ha := hh a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert has, Finset.sum_insert has, rightConv_add_right hφ ha.1 ha.2 hs.1 hs.2,
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

private theorem funext_comp_inv_mul_of_forall_apply_mul_inv {β : AdelicGL2 (𝓞 F) F → ℂ} {cst : ℂ} (t : AdelicGL2
    (𝓞 F) F)
    (ht : ∀ g : AdelicGL2 (𝓞 F) F, β (g * t)⁻¹ = cst * β g⁻¹) : (fun y => β (t⁻¹ * y)) = fun y => cst * β y := by
  funext y
  have := ht y⁻¹
  rwa [_root_.mul_inv_rev, _root_.inv_inv] at this

private theorem hasArchCharacterAt₀_rightConv_of_isArchBiFinite_ofChar {φ : AdelicGL2 (𝓞 F) F → ℂ}
    {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {β : AdelicGL2 (𝓞 F) F → ℂ}
    (hβ : IsArchBiFinite F (ArchTypeFamily.ofChar F χ) β) (w : InfinitePlace F) :
    HasArchCharacterAt₀ F w (χ w) (rightConv F φ β) := by
  have hinv : HasArchCharacterAt₀ F w (χ w) fun x => β x⁻¹ :=
    (mem_archCutSubmodule_ofChar_iff (F := F) χ _).mp hβ.1 w
  intro k g
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, funext_comp_inv_mul_of_forall_apply_mul_inv _ (hinv k),
    rightConv_const_mul_right, Pi.smul_apply, smul_eq_mul]

private theorem mem_archCutSubmodule_rightConv_of_isArchBiFinite_ofChar (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {β : AdelicGL2 (𝓞 F) F → ℂ}
    (hβ : IsArchBiFinite F (ArchTypeFamily.ofChar F χ) β) :
    rightConv F φ β ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) :=
  (mem_archCutSubmodule_ofChar_iff (F := F) χ _).mpr fun w =>
    hasArchCharacterAt₀_rightConv_of_isArchBiFinite_ofChar hβ w

private theorem exists_finsupp_sum_eq_of_tendsto_of_finiteDimensional {M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hM : FiniteDimensional ℂ M) (a : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (ha : ∀ n, a n ∈ M) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : ∀ g, Filter.Tendsto (fun n => a n g) Filter.atTop (nhds (f g))) :
    ∃ c : ℕ →₀ ℂ, (c.sum fun n cn => cn • a n) = f := by
  haveI := hM
  have hle : Submodule.span ℂ (Set.range a) ≤ M := Submodule.span_le.mpr (Set.range_subset_iff.mpr ha)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range a)) := Submodule.finiteDimensional_of_le hle
  have hclosed : IsClosed ((Submodule.span ℂ (Set.range a) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
      Set (AdelicGL2 (𝓞 F) F → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : f ∈ Submodule.span ℂ (Set.range a) :=
    hclosed.mem_of_tendsto (tendsto_pi_nhds.mpr hf)
      (Filter.Eventually.of_forall fun n => Submodule.subset_span ⟨n, rfl⟩)
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp hmem

section IsotypyOfConvolutions

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

private theorem isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ (rightConv ℚ φ f) :=
  isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre c u d₁ d₂ T hd hcov Φ
    (realizationOfIsIsotypicCuspFormAt hφ hne) hφ.continuous f hf hfs

private theorem ringHom_eq_id_ringOfIntegers_rat (e : 𝓞 ℚ →+* 𝓞 ℚ) : e = RingHom.id (𝓞 ℚ) := by
  have h : e.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  refine RingHom.ext fun x => ?_
  have h2 : e (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x))
      = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x) :=
    RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2

private theorem map_algebraMap_ringOfIntegers_rat (inst : Algebra (𝓞 ℚ) (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) :
    Ideal.map (@algebraMap (𝓞 ℚ) (𝓞 ℚ) _ _ inst) N = N := by
  rw [ringHom_eq_id_ringOfIntegers_rat (@algebraMap (𝓞 ℚ) (𝓞 ℚ) _ _ inst), Ideal.map_id]

private theorem exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (harch : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ),
      IsArchTestFactor ℚ fa ∧ IsFinTestFactor ℚ ff ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ (tensorTestFn fa ff) = φ := by
  classical

  have hlevel : Φ.level ≠ 0 := by simpa using Φ.level_ne_bot
  obtain ⟨S', hNS⟩ :
      ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p : HeightOneSpectrum (𝓞 ℚ), p.asIdeal ∣ Φ.level → p ∈ S' :=
    ⟨(Ideal.finite_factors hlevel).toFinset, fun _ hp => (Set.Finite.mem_toFinset _).mpr hp⟩

  obtain ⟨ff, fa, hff, hffs, hfa, htype, htend⟩ :=
    exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule ℚ ℚ Φ.level S' hNS
      (ArchTypeFamily.ofChar ℚ χ) φ hφ.continuous
      (by
        intro g k hk
        rw [map_algebraMap_ringOfIntegers_rat] at hk
        exact hφ.level_invariant g k hk)
      harch
  rw [map_algebraMap_ringOfIntegers_rat] at hffs

  have hmemM : ∀ n, rightConv ℚ φ (tensorTestFn (fa n) ff) ∈
      isotypicCuspSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ ⊓ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
    intro n
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact (isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ hφ hne _
        (isFactorizableTestFn_tensorTestFn (hfa n) hff)
        (tensorTestFn_support_of_forall hffs)).mem_isotypicCuspSubmodule
    · exact mem_archCutSubmodule_rightConv_of_isArchBiFinite_ofChar φ (htype n).isArchBiFinite
  have hfin := finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule ℚ c u d₁ d₂ T hd hcov ξ Φ.level
    Φ.level_ne_bot S (ArchTypeFamily.ofChar ℚ χ) Φ
  obtain ⟨cf, hcf⟩ := exists_finsupp_sum_eq_of_tendsto_of_finiteDimensional hfin
    (fun n => rightConv ℚ φ (tensorTestFn (fa n) ff)) hmemM htend

  refine ⟨∑ n ∈ cf.support, cf n • fa n, ff, isArchTestFactor_finset_sum _ _ hfa, hff, hffs, ?_⟩
  have hterm : ∀ n ∈ cf.support, Continuous (cf n • tensorTestFn (fa n) ff) ∧
      HasCompactSupport (cf n • tensorTestFn (fa n) ff) := by
    intro n _
    rw [← tensorTestFn_smul]
    exact continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _
      (isFactorizableTestFn_tensorTestFn ((isArchTestFactor_smul (hfa n)) (cf n)) hff)
  rw [tensorTestFn_finset_sum_smul, rightConv_finset_sum_right hφ.continuous _ hterm]
  simp only [rightConv_smul_right]
  simpa only [Finsupp.sum] using hcf

private theorem exists_isFactorizableTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ) (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) (harch : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    ∃ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, γ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ γ = φ := by
  obtain ⟨fa, ff, hfa, hff, hffs, hrep⟩ :=
    exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ χ hφ hne harch
  exact ⟨tensorTestFn fa ff, isFactorizableTestFn_tensorTestFn hfa hff, tensorTestFn_support_of_forall hffs, hrep⟩

private theorem isIsotypicCuspFormAt_add_smul_comb_of_rightConv_tensorTestFn
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    {ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ φ)
    (hne : φ ≠ 0) {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) (hff : IsFinTestFactor ℚ ff)
    (hffs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ff (glFin (𝓞 ℚ) ℚ x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hrep : rightConv ℚ φ (tensorTestFn fa ff) = φ) {w : InfinitePlace ℚ} (hw : w.IsReal) (cH cE cF c₀ : ℂ)
    {t : AdelicGL2 (𝓞 ℚ) ℚ} (ht : glFin (𝓞 ℚ) ℚ t = 1) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Φ.level S Φ
      (φ + c₀ • fun g =>
        (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ) (g * t)) := by

  have hder : ∀ d : ArchDir, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ, IsArchTestFactor ℚ fa' ∧
      archDerivAt hw d φ = rightConv ℚ φ (tensorTestFn fa' ff) := by
    intro d
    obtain ⟨-, heq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn ℚ hw d).1 φ _
      hφ.continuous (isFactorizableTestFn_tensorTestFn hfa hff)
    obtain ⟨fa', hfa', hfa'eq⟩ :=
      (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn ℚ hw d).2.1 fa ff hfa
    refine ⟨fa', hfa', ?_⟩
    rw [hrep] at heq
    rw [heq]
    exact congrArg (rightConv ℚ φ) hfa'eq
  obtain ⟨fH, hfH, hH⟩ := hder .H
  obtain ⟨fE, hfE, hE⟩ := hder .E
  obtain ⟨fF, hfF, hF⟩ := hder .Fm
  have hcs : ∀ fa₀ : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ, IsArchTestFactor ℚ fa₀ →
      Continuous (tensorTestFn fa₀ ff) ∧ HasCompactSupport (tensorTestFn fa₀ ff) := fun _ h =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _ (isFactorizableTestFn_tensorTestFn h hff)
  have hfX : IsArchTestFactor ℚ (cH • fH + cE • fE + cF • fF) := (isArchTestFactor_add ((isArchTestFactor_add
      ((isArchTestFactor_smul hfH) cH)) ((isArchTestFactor_smul hfE) cE))) ((isArchTestFactor_smul hfF) cF)

  have h1 : rightConv ℚ φ (tensorTestFn (cH • fH) ff) = cH • archDerivAt hw .H φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hH]
  have h2 : rightConv ℚ φ (tensorTestFn (cE • fE) ff) = cE • archDerivAt hw .E φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hE]
  have h3 : rightConv ℚ φ (tensorTestFn (cF • fF) ff) = cF • archDerivAt hw .Fm φ := by
    rw [tensorTestFn_smul, rightConv_smul_right, hF]
  have h12 : rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE) ff) =
      cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ ((isArchTestFactor_smul hfH) cH)).1 (hcs _
            ((isArchTestFactor_smul hfH) cH)).2
      (hcs _ ((isArchTestFactor_smul hfE) cE)).1 (hcs _ ((isArchTestFactor_smul hfE) cE)).2, h1, h2]
  have hcomb : rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE + cF • fF) ff) =
      cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ ((isArchTestFactor_add ((isArchTestFactor_smul hfH) cH))
            ((isArchTestFactor_smul hfE) cE))).1
      (hcs _ ((isArchTestFactor_add ((isArchTestFactor_smul hfH) cH)) ((isArchTestFactor_smul hfE) cE))).2 (hcs
          _ ((isArchTestFactor_smul hfF) cF)).1 (hcs _ ((isArchTestFactor_smul hfF) cF)).2, h12, h3]

  have htr : (fun g => rightConv ℚ φ (tensorTestFn (cH • fH + cE • fE + cF • fF) ff) (g * t)) =
      rightConv ℚ φ (tensorTestFn (fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x)) ff) := by
    funext g
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    exact congrFun (congrArg (rightConv ℚ φ) (tensorTestFn_comp_inv_mul_of_glFin_eq_one _ _ ht)) g
  have hXt : IsArchTestFactor ℚ fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x) :=
    (isArchTestFactor_comp_mul_left hfX) (glArch (𝓞 ℚ) ℚ t)⁻¹

  have hfinal : rightConv ℚ φ
      (tensorTestFn (fa + c₀ • fun x => (cH • fH + cE • fE + cF • fF) ((glArch (𝓞 ℚ) ℚ t)⁻¹ * x)) ff) =
        φ + c₀ • fun g =>
          (cH • archDerivAt hw .H φ + cE • archDerivAt hw .E φ + cF • archDerivAt hw .Fm φ) (g * t) := by
    rw [tensorTestFn_add,
        rightConv_add_right hφ.continuous (hcs _ hfa).1 (hcs _ hfa).2 (hcs _ ((isArchTestFactor_smul hXt) c₀)).1
      (hcs _ ((isArchTestFactor_smul hXt) c₀)).2, hrep, tensorTestFn_smul, rightConv_smul_right, ← hcomb, ← htr]
  rw [← hfinal]
  exact isIsotypicCuspFormAt_rightConv_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ hφ hne _
    (isFactorizableTestFn_tensorTestFn ((isArchTestFactor_add hfa) ((isArchTestFactor_smul hXt) c₀)) hff)
        (tensorTestFn_support_of_forall hffs)

end IsotypyOfConvolutions

end

end IsotypicReproduction

section CoefficientIntegrability

open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

private theorem exists_archDerivAt_eq_rightConv_tensorTestFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) (hrep : rightConv F φ (tensorTestFn fa ff) = φ)
    {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa' ∧
      archDerivAt hw d φ = rightConv F φ (tensorTestFn fa' ff) := by
  obtain ⟨-, heq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ _ hφ
    (isFactorizableTestFn_tensorTestFn hfa hff)
  obtain ⟨fa', hfa', hfa'eq⟩ := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', ?_⟩
  rw [hrep] at heq
  rw [heq]
  exact congrArg (rightConv F φ) hfa'eq

private theorem whittakerCoefficientIntegrable_self_and_archDerivAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hcont : Continuous φ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) :
    (∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α g) ∧
      ∀ (d : ArchDir) (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) α g := by
  obtain ⟨α₀, hα₀, hrep₀⟩ := hconv
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := isFactorizableTestFn_exists_eq_tensorTestFn hα₀
  refine ⟨fun α g => ?_, fun d α g => ?_⟩
  · exact (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ φ hleft
      (isKfSmooth_of_exists_rightConv_eq ℚ φ ⟨_, isFactorizableTestFn_tensorTestFn hfa hff, hrep₀⟩)
      (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw hsm g)).1 α g
  · obtain ⟨fa', hfa', hd⟩ := exists_archDerivAt_eq_rightConv_tensorTestFn hcont hfa hff hrep₀ hw d
    have hleft' : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        archDerivAt hw d φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = archDerivAt hw d φ g := by
      intro β g
      have hfun : (fun x => φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * x)) = φ := funext fun x => hleft β x
      have := congrFun (archDerivAt_comp_mul_left hw d φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β))) g
      rw [hfun] at this
      exact this.symm
    have hKf : IsKfSmooth ℚ (archDerivAt hw d φ) := by
      rw [hd]
      exact isKfSmooth_rightConv ℚ φ _ (isFactorizableTestFn_tensorTestFn hfa' hff)
    exact (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff D U gen ψ hψ _ hleft' hKf
      (fun g => contDiff_two_unipotentGL2_ratArchLine_mul_of_isArchSmoothAt hw (hsm.archDerivAt d) g)).1 α g

end CoefficientIntegrability
end P2M.IsotypicSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule.P2M P2MW.S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule.P2M.IsotypicSmooth"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule.P2M"

open P2M.IsotypicSmooth in

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ φ)
    (hne : φ ≠ 0)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (harch : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) φ) :

    (∃ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, γ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ γ = φ) ∧

    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cH cE cF c₀ : ℂ) (t : AdelicGL2 (𝓞 ℚ) ℚ), glFin (𝓞 ℚ) ℚ t = 1 →
      IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ
        (φ + c₀ • fun g =>
          (cH • archDerivAt hw ArchDir.H φ + cE • archDerivAt hw ArchDir.E φ + cF • archDerivAt hw ArchDir.Fm φ)
            (g * t))) ∧

    (∀ ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ, IsGlobalAddChar ℚ ψ → ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ →
        (∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), WhittakerCoefficientIntegrable ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ φ α g) ∧
        (∀ (d : ArchDir) (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), WhittakerCoefficientIntegrable ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw d φ) α g) ∧
        ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ φ 1 g ≠ 0) ∧

    (∀ ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ, IsGlobalAddChar ℚ ψ →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
        ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
          ‖whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M) := by
  have hcut : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) :=
    (mem_archCutSubmodule_ofChar_iff (F := ℚ) _ _).mpr harch
  obtain ⟨fa, ff, hfa, hff, hffs, hrep⟩ :=
    exists_tensorTestFn_rightConv_eq_self_of_isIsotypicCuspFormAt c u d₁ d₂ T hd hcov Φ χ hiso hne hcut
  have hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ :=
    ⟨tensorTestFn fa ff, isFactorizableTestFn_tensorTestFn hfa hff, hrep⟩
  have hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g :=
    fun β g => apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt hiso β g
  refine ⟨⟨tensorTestFn fa ff, isFactorizableTestFn_tensorTestFn hfa hff, tensorTestFn_support_of_forall hffs, hrep⟩,
    fun w hw cH cE cF c₀ t ht =>
      isIsotypicCuspFormAt_add_smul_comb_of_rightConv_tensorTestFn c u d₁ d₂ T hd hcov Φ hiso hne hfa hff hffs hrep
        hw cH cE cF c₀ ht,
    fun ψ hψ w hw hsm => ?_, fun ψ hψ t ht => ?_⟩
  · obtain ⟨hint, hintd⟩ :=
      whittakerCoefficientIntegrable_self_and_archDerivAt _ _ _ ψ hψ hw hiso.continuous hleft hconv hsm
    exact ⟨hint, hintd, exists_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt _ _ _ ψ hψ hw hiso hsm hne⟩
  · exact exists_forall_norm_whittakerCoefficient_one_diagOne_mul_le_mul_ideleNorm_rpow c u d₁ d₂ T hd hcov hiso hne
      (isFactorizableTestFn_tensorTestFn hfa hff) hrep hcut hψ (Classical.arbitrary (InfinitePlace ℚ)) ht

end S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule (solution)
