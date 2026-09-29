-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/93c84ef2-7879-5f90-b203-2a8808be448e

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace GStab

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

private abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

private abbrev g5DetSet : Set Ent := {e : Ent | (Matrix.of e).det ≠ 0}

private theorem g5_isOpen_detSet : IsOpen g5DetSet := by
  have h : Continuous fun e : Ent => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

section LiftAnalysis

private def g5Inv (e : Ent) : Ent := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

private theorem g5_of_g5Inv {e : Ent} : Matrix.of (g5Inv e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [g5Inv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

private theorem g5_det_g5Inv {e : Ent} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (g5Inv e)).det ≠ 0 := by
  rw [g5_of_g5Inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem g5_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i).contDiff

private theorem g5_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((g5_contDiff_entry 0 0).mul (g5_contDiff_entry 1 1)).sub ((g5_contDiff_entry 0 1).mul (g5_contDiff_entry 1 0))

private theorem g5_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact g5_contDiff_entry _ _ | exact (g5_contDiff_entry _ _).neg

private theorem g5_contDiffOn_g5Inv : ContDiffOn ℝ (⊤ : ℕ∞) g5Inv g5DetSet :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    (g5_contDiff_adj i j).contDiffOn.div g5_contDiff_det.contDiffOn fun _ he => he

private theorem g5_g5Inv_mem {e : Ent} (he : e ∈ g5DetSet) : g5Inv e ∈ g5DetSet := g5_det_g5Inv he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem g5_lift_inv (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archRealLiftAt hw (g5Inv e) := by
  rw [archRealLiftAt_of_det_ne_zero hw he, archRealLiftAt_of_det_ne_zero hw (g5_det_g5Inv he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact g5_of_g5Inv.symm

private def g5Theta (hw : w.IsReal) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (archMatrixUpdate K w (A.map (ringEquivRealOfIsReal hw).symm) i j,
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j)

private theorem g5_coe_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ((archRealGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      g5Theta hw (m : Matrix (Fin 2) (Fin 2) ℝ) :=
  rfl

private theorem g5_continuous_Theta (hw : w.IsReal) : Continuous (g5Theta (K := K) hw) := by
  have hentry : ∀ i j : Fin 2, Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j := fun i j =>
    (continuous_apply j).comp (continuous_apply i : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i)
  have hsymm : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  refine continuous_matrix fun i j => Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [archMatrixUpdate_apply_self, Matrix.map_apply]
    exact hsymm.comp (hentry i j)
  · simp only [archMatrixUpdate_apply_of_ne K w _ i j hv]
    exact continuous_const

private theorem g5_continuousOn_lift (hw : w.IsReal) :
    ContinuousOn (fun e : Ent => (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)) g5DetSet := by
  rw [continuousOn_iff_continuous_restrict]
  have hdet : ∀ e : g5DetSet, (Matrix.of (e : Ent)).det ≠ 0 := fun e => e.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : g5DetSet,
        ((archRealLiftAt hw (e : Ent) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          g5Theta hw (Matrix.of (e : Ent)) := fun e => by
      rw [archRealLiftAt_of_det_ne_zero hw (hdet e), g5_coe_archRealGLAt]
      rfl
    exact ((g5_continuous_Theta hw).comp continuous_subtype_val).congr fun e => (h e).symm
  · have h : ∀ e : g5DetSet,
        (((archRealLiftAt hw (e : Ent) : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = g5Theta hw (Matrix.of (g5Inv (e : Ent))) := fun e => by
      rw [g5_lift_inv hw (hdet e), archRealLiftAt_of_det_ne_zero hw (g5_det_g5Inv (hdet e)), g5_coe_archRealGLAt]
      rfl
    exact ((g5_continuous_Theta hw).comp
      (continuousOn_iff_continuous_restrict.1 g5_contDiffOn_g5Inv.continuousOn)).congr fun e => (h e).symm

end LiftAnalysis

section AffineData

open scoped Classical

section FieldOnly

variable (K : Type) [Field K]

private abbrev g5Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private theorem g5_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem g5_continuous_archEntries : Continuous (archEntries K) := by
  have hval : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      (a.val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => (g5_continuous_ringEquiv K).comp ?_
  exact (continuous_apply j).comp
    ((continuous_apply i : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m i).comp hval)

private theorem g5_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

private theorem g5_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  g5_archEntries_eq_mapMatrix K g

private theorem g5_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [g5_of_archEntries, Units.val_mul, map_mul]

variable {K}

private def g5single (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

private theorem g5_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) :
    archMatrixUpdate K w m i j = archMatrixUpdate K w 0 i j + g5single w (m i j) := by
  funext v
  show archMatrixUpdate K w m i j v =
    archMatrixUpdate K w 0 i j v + Pi.single (M := fun v : InfinitePlace K => v.Completion) w (m i j) v
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self, archMatrixUpdate_apply_self, Pi.single_eq_same, Matrix.zero_apply, zero_add]
  · rw [archMatrixUpdate_apply_of_ne K w m i j hv, archMatrixUpdate_apply_of_ne K w 0 i j hv, Pi.single_eq_of_ne hv,
      add_zero]

private def g5Const (w : InfinitePlace K) : g5Ent K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

private theorem g5_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      g5Const w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (g5single w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [g5_archMatrixUpdate_entry, map_add]
  rfl

private def g5AddHom {w : InfinitePlace K} (hw : w.IsReal) : ℝ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivRealOfIsReal hw).symm.toAddMonoidHom)

private theorem g5AddHom_apply {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    g5AddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (g5single w ((ringEquivRealOfIsReal hw).symm r)) :=
  rfl

private theorem g5_continuous_addHom {w : InfinitePlace K} (hw : w.IsReal) : Continuous (g5AddHom hw) := by
  have h1 : Continuous fun x : w.Completion => g5single w x := continuous_single w
  have h2 : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  have h3 : ⇑(g5AddHom hw) = fun r : ℝ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (g5single w ((ringEquivRealOfIsReal hw).symm r)) :=
    funext fun r => g5AddHom_apply hw r
  rw [h3]
  exact (g5_continuous_ringEquiv K).comp (h1.comp h2)

private def g5Lin {w : InfinitePlace K} (hw : w.IsReal) : ℝ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (g5AddHom hw).toRealLinearMap (g5_continuous_addHom hw)

private def g5LinMat {w : InfinitePlace K} (hw : w.IsReal) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] g5Ent K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (g5Lin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

private theorem g5LinMat_apply {w : InfinitePlace K} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    g5LinMat hw e i j = g5AddHom hw (e i j) :=
  rfl

end FieldOnly

section NumberFieldPart

variable {K : Type} [Field K] [NumberField K]

private theorem g5_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e)) = g5Const w + g5LinMat hw e := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  have h1 : glArch (𝓞 K) K (archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) :=
    glArch_adelicArchGLIncl K _
  rw [h1]
  funext i j
  rw [g5_archEntries_archGLIncl, glEquivOfRingEquiv_apply_entry, Pi.add_apply, Pi.add_apply, g5LinMat_apply,
    g5AddHom_apply]
  rfl

end NumberFieldPart

end AffineData

section TestData

open MeasureTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem g5_glFin_lift (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archRealLiftAt hw e) = 1 := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

private theorem g5_glFin_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 K) K (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl K _

private def g5MulRLin (M : g5Ent K) : g5Ent K →ₗ[ℝ] g5Ent K where
  toFun N := Matrix.of.symm (Matrix.of N * Matrix.of M)
  map_add' N₁ N₂ := by
    show Matrix.of.symm ((Matrix.of N₁ + Matrix.of N₂) * Matrix.of M) =
      Matrix.of.symm (Matrix.of N₁ * Matrix.of M) + Matrix.of.symm (Matrix.of N₂ * Matrix.of M)
    rw [Matrix.add_mul]
    rfl
  map_smul' t N := by
    show Matrix.of.symm ((t • Matrix.of N) * Matrix.of M) = t • Matrix.of.symm (Matrix.of N * Matrix.of M)
    rw [Matrix.smul_mul]
    rfl

private def g5MulR (M : g5Ent K) : g5Ent K →L[ℝ] g5Ent K := LinearMap.toContinuousLinearMap (g5MulRLin M)

private theorem g5MulR_apply (M N : g5Ent K) : g5MulR M N = Matrix.of.symm (Matrix.of N * Matrix.of M) := rfl

private def g5MulRL : g5Ent K →ₗ[ℝ] (g5Ent K →L[ℝ] g5Ent K) where
  toFun := g5MulR
  map_add' M₁ M₂ := by
    refine ContinuousLinearMap.ext fun N => ?_
    show Matrix.of.symm (Matrix.of N * (Matrix.of M₁ + Matrix.of M₂)) =
      Matrix.of.symm (Matrix.of N * Matrix.of M₁) + Matrix.of.symm (Matrix.of N * Matrix.of M₂)
    rw [Matrix.mul_add]
    rfl
  map_smul' t M := by
    refine ContinuousLinearMap.ext fun N => ?_
    show Matrix.of.symm (Matrix.of N * (t • Matrix.of M)) = t • Matrix.of.symm (Matrix.of N * Matrix.of M)
    rw [Matrix.mul_smul]
    rfl

private theorem g5_continuous_mulR : Continuous (g5MulR : g5Ent K → g5Ent K →L[ℝ] g5Ent K) :=
  (g5MulRL (K := K)).continuous_of_finiteDimensional

private def g5MulLLin (A : g5Ent K) : g5Ent K →ₗ[ℝ] g5Ent K where
  toFun N := Matrix.of.symm (Matrix.of A * Matrix.of N)
  map_add' N₁ N₂ := by
    show Matrix.of.symm (Matrix.of A * (Matrix.of N₁ + Matrix.of N₂)) =
      Matrix.of.symm (Matrix.of A * Matrix.of N₁) + Matrix.of.symm (Matrix.of A * Matrix.of N₂)
    rw [Matrix.mul_add]
    rfl
  map_smul' t N := by
    show Matrix.of.symm (Matrix.of A * (t • Matrix.of N)) = t • Matrix.of.symm (Matrix.of A * Matrix.of N)
    rw [Matrix.mul_smul]
    rfl

private def g5MulL (A : g5Ent K) : g5Ent K →L[ℝ] g5Ent K := LinearMap.toContinuousLinearMap (g5MulLLin A)

private theorem g5MulL_apply (A N : g5Ent K) : g5MulL A N = Matrix.of.symm (Matrix.of A * Matrix.of N) := rfl

private theorem g5_archEntries_lift_mul (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y)) =
      g5MulR (archEntries K (glArch (𝓞 K) K y)) (g5Const w) +
        g5MulR (archEntries K (glArch (𝓞 K) K y)) (g5LinMat hw e) := by
  rw [g5MulR_apply, g5MulR_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y))), map_mul,
    g5_archEntries_mul, g5_archEntries_glArch_lift hw he]
  show Matrix.of.symm ((Matrix.of (g5Const w) + Matrix.of (g5LinMat hw e)) *
    Matrix.of (archEntries K (glArch (𝓞 K) K y))) = _
  rw [Matrix.add_mul]
  rfl

private theorem g5_factor_lift_mul (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (archRealLiftAt hw e * y) =
      Φ (g5MulR (archEntries K (glArch (𝓞 K) K y)) (g5Const w) +
          g5MulR (archEntries K (glArch (𝓞 K) K y)) (g5LinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, g5_archEntries_lift_mul hw he, map_mul, g5_glFin_lift hw he, one_mul]

end TestData

section Curves

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem g5_archFlowAt_inv (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

private def g5Curve (d : ArchDir) (t : ℝ) : Ent :=
  Matrix.of.symm
    (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))

private theorem g5_curve_mem (d : ArchDir) (t : ℝ) : g5Curve d t ∈ g5DetSet := by
  show (Matrix.of (g5Curve d t)).det ≠ 0
  rw [g5Curve, Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix d t).isUnit).ne_zero

private theorem g5_hasDerivAt_curve (d : ArchDir) :
    HasDerivAt (g5Curve d)
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 :=
  hasDerivAt_of_symm_mul_archFlowMatrix _ d

private theorem g5_archFlowAt_eq_lift (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) = archRealLiftAt hw (g5Curve d t) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [g5Curve, ← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]

private def g5Dir (d : ArchDir) : Ent :=
  (-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)

private theorem g5_hasDerivAt_curve_neg (d : ArchDir) : HasDerivAt (fun t : ℝ => g5Curve d (-t)) (g5Dir d) 0 := by
  have h := g5_hasDerivAt_curve d
  rw [← neg_zero] at h
  exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

private theorem g5_curve_det (d : ArchDir) (t : ℝ) : (Matrix.of (g5Curve d t)).det ≠ 0 := g5_curve_mem d t

end Curves

section Twist

set_option linter.unusedSectionVars false

open scoped Classical
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal)

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def g5B (hw : w.IsReal) (y : AdelicGL2 (𝓞 K) K) : Ent →L[ℝ] g5Ent K :=
  (g5MulR (archEntries K (glArch (𝓞 K) K y))).comp (g5LinMat hw)

private def g5P (y : AdelicGL2 (𝓞 K) K) : g5Ent K := g5MulR (archEntries K (glArch (𝓞 K) K y)) (g5Const w)

private theorem g5_hasDerivAt_lift_curve (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    {c : ℝ → Ent} {c' : Ent} (hc : HasDerivAt c c' 0) (hdet : ∀ t, (Matrix.of (c t)).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => α (archRealLiftAt hw (c t) * y))
      ((fderiv ℝ Φ (g5P (w := w) y + g5B hw y (c 0))) (g5B hw y c') * ff (glFin (𝓞 K) K y)) 0 := by
  have hfun : (fun t : ℝ => α (archRealLiftAt hw (c t) * y)) =
      fun t => Φ (g5P (w := w) y + g5B hw y (c t)) * ff (glFin (𝓞 K) K y) := by
    funext t
    rw [g5_factor_lift_mul hw hfa hα (hdet t) y]
    rfl
  rw [hfun]
  have hinner : HasDerivAt (fun t : ℝ => g5P (w := w) y + g5B hw y (c t)) (g5B hw y c') 0 :=
    ((g5B hw y).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc).const_add _
  have hdiff : DifferentiableAt ℝ Φ (g5P (w := w) y + g5B hw y (c 0)) := (hΦ.differentiable (by simp)).differentiableAt
  exact (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinner).mul_const _

private theorem g5_leftDeriv_eq (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (d : ArchDir) (y : AdelicGL2 (𝓞 K) K) :
    deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 =
      (fderiv ℝ Φ (g5P (w := w) y + g5B hw y (Matrix.of.symm 1))) (g5B hw y (g5Dir d)) * ff (glFin (𝓞 K) K y) := by
  have h := g5_hasDerivAt_lift_curve hw hΦ hfa hα (g5_hasDerivAt_curve_neg d) (fun t => g5_curve_det d (-t)) y
  have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) = fun t => α (archRealLiftAt hw (g5Curve d (-t)) * y) := by
    funext t; rw [g5_archFlowAt_eq_lift]
  have h0 : g5Curve d (-0) = Matrix.of.symm 1 := by
    rw [neg_zero, g5Curve, archFlowMatrix_zero]
    simp
  rw [hfun, h.deriv, h0]

private def kr (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) ℝ :=
  glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)

private theorem kr_mem (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) : kr hw k ∈ rowIsometrySubgroup₀ ℝ :=
  (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k).2

private theorem rowIsometryInclAt₀_eq_archRealGLAt (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ K w k = archRealGLAt hw (kr hw k) := by
  rw [rowIsometryInclAt₀_apply, kr, archRealGLAt_glEquivOfRingEquiv]

private theorem archWeightOneAt_eq (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightOneAt hw k : ℂˣ) : ℂ) =
      ⟨((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0, ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩ :=
  rfl

private def twCurve (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) (t : ℝ) : Ent :=
  Matrix.of.symm (((kr hw k)⁻¹ : GL (Fin 2) ℝ) * (archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) *
    ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))

private theorem twCurve_det (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) (t : ℝ) :
    (Matrix.of (twCurve hw k d t)).det ≠ 0 := by
  rw [twCurve, Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 ((kr hw k)⁻¹).isUnit).ne_zero
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix d (-t)).isUnit).ne_zero
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (kr hw k).isUnit).ne_zero

private theorem twCurve_zero (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) :
    twCurve hw k d 0 = Matrix.of.symm 1 := by
  rw [twCurve, neg_zero, archFlowMatrix_zero]
  simp

private def conjCLM (A B : Matrix (Fin 2) (Fin 2) ℝ) : Ent →L[ℝ] Ent :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm (A * Matrix.of e * B)
      map_add' := fun e e' => by
        show Matrix.of.symm (A * (Matrix.of e + Matrix.of e') * B) = Matrix.of.symm (A * Matrix.of e * B) + Matrix.of.symm (A * Matrix.of e' * B)
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c e => by
        show Matrix.of.symm (A * (c • Matrix.of e) * B) = c • Matrix.of.symm (A * Matrix.of e * B)
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }

private theorem conjCLM_apply (A B : Matrix (Fin 2) (Fin 2) ℝ) (e : Ent) :
    conjCLM A B e = Matrix.of.symm (A * Matrix.of e * B) := rfl

private theorem hasDerivAt_twCurve (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) :
    HasDerivAt (twCurve hw k d)
      (Matrix.of.symm (-((((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
        ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))) 0 := by

  have h1 : HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (-archDirMatrix d)) 0 := by
    have h := hasDerivAt_of_symm_mul_archFlowMatrix (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) d
    simp only [Equiv.apply_symm_apply, one_mul] at h
    rw [← neg_zero] at h
    have h' := h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    convert h' using 1 <;> first | rfl | (rw [neg_one_smul]; rfl)
  have h2 := (conjCLM (((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hfun : twCurve hw k d = (conjCLM (((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∘ fun t : ℝ => Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext t
    rfl
  rw [hfun]
  convert h2 using 1 <;> first | rfl | rw [conjCLM_apply, Equiv.apply_symm_apply, Matrix.mul_neg, Matrix.neg_mul]

private theorem archFlowAt_mul_rowIsometryInclAt₀ (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d (-t) : AdelicGL2 (𝓞 K) K) * rowIsometryInclAt₀ K w k =
      rowIsometryInclAt₀ K w k * archRealLiftAt hw (twCurve hw k d t) := by
  rw [rowIsometryInclAt₀_eq_archRealGLAt hw k, archRealLiftAt_of_det_ne_zero hw (twCurve_det hw k d t), archFlowAt,
    ← map_mul, ← map_mul]
  congr 1
  have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of (twCurve hw k d t)) (twCurve_det hw k d t) =
      (kr hw k)⁻¹ * archFlowMatrix d (-t) * kr hw k := by
    apply Units.ext
    show Matrix.of (twCurve hw k d t) = _
    rw [twCurve, Equiv.apply_symm_apply, Units.val_mul, Units.val_mul]
  rw [hmk, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

end Twist

section AdAlgebra

set_option linter.unusedSectionVars false

open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal)

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def twDir (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) (d : ArchDir) : Ent :=
  Matrix.of.symm (-((((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
    ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))

private theorem g5Dir_eq (d : ArchDir) : g5Dir d = Matrix.of.symm (-archDirMatrix d) := by
  rw [g5Dir]
  simp only [Equiv.apply_symm_apply, one_mul, neg_smul, one_smul]
  rfl

private theorem kr_coe (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0, ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
        -((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1, ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
  obtain ⟨h10, h11, -⟩ := entries_of_mem_rowIsometrySubgroup₀ (kr_mem hw k)
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact h10
  · exact h11

private theorem kr_inv_coe (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    (((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0, -((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
        ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1, ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
  obtain ⟨-, -, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ (kr_mem hw k)
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_left_inv ?_
  conv_lhs => rw [kr_coe hw k]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hab]

private theorem twDir_eq (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    twDir hw k .H = ((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2 - (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ^ 2) • g5Dir .H +
        (2 * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1)) • (g5Dir .E + g5Dir .Fm) ∧
      twDir hw k .E = (-((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1))) • g5Dir .H +
        ((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2) • g5Dir .E + (-((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ^ 2)) • g5Dir .Fm ∧
      twDir hw k .Fm = (-((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1))) • g5Dir .H +
        (-((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ^ 2)) • g5Dir .E + ((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2) • g5Dir .Fm := by
  set a := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  have hk : ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] := kr_coe hw k
  have hki : (((kr hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, -b; b, a] := kr_inv_coe hw k
  simp only [twDir, g5Dir_eq, hki, hk]
  refine ⟨?_, ?_, ?_⟩ <;>
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [archDirMatrix] <;> ring

private theorem archWeightOneAt_mk (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightOneAt hw k : ℂˣ) : ℂ) =
      (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * Complex.I := by
  rw [archWeightOneAt_eq, Complex.mk_eq_add_mul_I]

private theorem archWeightOneAt_normSq (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ^ 2 + (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ^ 2 = 1 :=
  (entries_of_mem_rowIsometrySubgroup₀ (kr_mem hw k)).2.2

private theorem archWeightCharAt_coe (hw : w.IsReal) (m : ℤ) (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightCharAt hw m k : ℂˣ) : ℂ) = ((archWeightOneAt hw k : ℂˣ) : ℂ) ^ m := by
  show (((zpowGroupHom m) (archWeightOneAt hw k) : ℂˣ) : ℂ) = _
  rw [zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]

end AdAlgebra

section LeftLaw

set_option linter.unusedSectionVars false

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

private def Ld (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0

private def βs (s : ℂ) (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => Ld hw .H α y + s * (Ld hw .E α y + Ld hw .Fm α y)

private theorem βs_left_w {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    {cχ : rowIsometrySubgroup₀ w.Completion → ℂ} (hαL : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z : AdelicGL2 (𝓞 K) K),
      α (rowIsometryInclAt₀ K w k * z) = cχ k * α z)
    {s : ℂ} (hs : s ^ 2 = -1) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K) :
    βs hw s α (rowIsometryInclAt₀ K w k * y) =
      cχ k * (((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) ^ 2 - (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) ^ 2) -
        2 * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * s) * βs hw s α y := by
  set a := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set q : g5Ent K := g5P (w := w) y + g5B hw y (Matrix.of.symm 1) with hq
  set Λ : Ent → ℂ := fun e => (fderiv ℝ Φ q) (g5B hw y e) * ff (glFin (𝓞 K) K y) with hΛ
  have hΛ_add : ∀ e e', Λ (e + e') = Λ e + Λ e' := fun e e' => by
    simp only [hΛ, map_add, add_mul]
  have hΛ_smul : ∀ (r : ℝ) e, Λ (r • e) = (r : ℂ) * Λ e := fun r e => by
    simp only [hΛ, map_smul, Complex.real_smul, mul_assoc]
  have hL : ∀ d, Ld hw d α y = Λ (g5Dir d) := fun d => g5_leftDeriv_eq hw hΦ hfa hα d y
  have hT : ∀ d, Ld hw d α (rowIsometryInclAt₀ K w k * y) = cχ k * Λ (twDir hw k d) := by
    intro d
    have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * (rowIsometryInclAt₀ K w k * y))) =
        fun t => cχ k * α (archRealLiftAt hw (twCurve hw k d t) * y) := by
      funext t
      rw [← mul_assoc, archFlowAt_mul_rowIsometryInclAt₀, mul_assoc, hαL]
    have hd := ((g5_hasDerivAt_lift_curve hw hΦ hfa hα (hasDerivAt_twCurve hw k d) (twCurve_det hw k d) y).const_mul
      (cχ k)).deriv
    show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * (rowIsometryInclAt₀ K w k * y))) 0 = _
    rw [hfun, hd, twCurve_zero]
    rfl
  obtain ⟨eH, eE, eF⟩ := twDir_eq hw k
  have hβ1 : βs hw s α (rowIsometryInclAt₀ K w k * y) =
      cχ k * Λ (twDir hw k .H) + s * (cχ k * Λ (twDir hw k .E) + cχ k * Λ (twDir hw k .Fm)) := by
    simp only [βs, hT]
  have hβ0 : βs hw s α y = Λ (g5Dir .H) + s * (Λ (g5Dir .E) + Λ (g5Dir .Fm)) := by
    simp only [βs, hL]
  rw [hβ1, hβ0, eH, eE, eF]
  simp only [hΛ_add, hΛ_smul]
  push_cast
  linear_combination (cχ k * 2 * (a : ℂ) * (b : ℂ) * (Λ (g5Dir .E) + Λ (g5Dir .Fm))) * hs

end LeftLaw

section Step

set_option linter.unusedSectionVars false

open scoped Classical
open MeasureTheory NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain AutomorphicForm.CuspidalConstituent

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

private theorem Ld_right_law {γ : AdelicGL2 (𝓞 K) K → ℂ} {g₀ : AdelicGL2 (𝓞 K) K} {cc : ℂ}
    (h : ∀ g, γ (g * g₀) = cc * γ g) (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) : Ld hw d γ (g * g₀) = cc * Ld hw d γ g := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (g * g₀))) 0 = cc * deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * g)) 0
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * (g * g₀))) = fun t => cc * γ (archFlowAt hw d (-t) * g) := by
    funext t; rw [← mul_assoc, h]
  rw [hfun]
  exact deriv_const_mul_field cc

private theorem Ld_left_law {γ : AdelicGL2 (𝓞 K) K → ℂ} {g₀ : AdelicGL2 (𝓞 K) K} {cc : ℂ}
    (hcomm : ∀ (d : ArchDir) (t : ℝ), archFlowAt hw d t * g₀ = g₀ * archFlowAt hw d t)
    (h : ∀ z, γ (g₀ * z) = cc * γ z) (d : ArchDir) (y : AdelicGL2 (𝓞 K) K) : Ld hw d γ (g₀ * y) = cc * Ld hw d γ y := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (g₀ * y))) 0 = cc * deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * (g₀ * y))) = fun t => cc * γ (archFlowAt hw d (-t) * y) := by
    funext t; rw [← mul_assoc, hcomm, mul_assoc, h]
  rw [hfun]
  exact deriv_const_mul_field cc

private theorem βs_right_law (s : ℂ) {γ : AdelicGL2 (𝓞 K) K → ℂ} {g₀ : AdelicGL2 (𝓞 K) K} {cc : ℂ}
    (h : ∀ g, γ (g * g₀) = cc * γ g) (g : AdelicGL2 (𝓞 K) K) : βs hw s γ (g * g₀) = cc * βs hw s γ g := by
  simp only [βs, Ld_right_law hw h]
  ring

private theorem βs_left_law (s : ℂ) {γ : AdelicGL2 (𝓞 K) K → ℂ} {g₀ : AdelicGL2 (𝓞 K) K} {cc : ℂ}
    (hcomm : ∀ (d : ArchDir) (t : ℝ), archFlowAt hw d t * g₀ = g₀ * archFlowAt hw d t)
    (h : ∀ z, γ (g₀ * z) = cc * γ z) (y : AdelicGL2 (𝓞 K) K) : βs hw s γ (g₀ * y) = cc * βs hw s γ y := by
  simp only [βs, Ld_left_law hw hcomm h]
  ring

private theorem archFlowAt_comm_of_ne {v : InfinitePlace K} (hvw : v ≠ w) (k : rowIsometrySubgroup₀ v.Completion)
    (d : ArchDir) (t : ℝ) :
    archFlowAt hw d t * rowIsometryInclAt₀ K v k = rowIsometryInclAt₀ K v k * archFlowAt hw d t := by
  rw [rowIsometryInclAt₀_apply]
  exact ((commute_adelicArchGLInclAt_of_ne K hvw (k : GL (Fin 2) v.Completion) _).eq).symm

private theorem archFlowAt_comm_of_glArch {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) (d : ArchDir) (t : ℝ) :
    archFlowAt hw d t * k = k * archFlowAt hw d t :=
  archFlowAt_mul_comm_of_glArch_eq_one hw d t hk

private theorem weight_shift (n σ : ℤ) (s : ℂ) (hsσ : (s = -Complex.I ∧ σ = -2) ∨ (s = Complex.I ∧ σ = 2))
    (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightCharAt hw (n + σ) k⁻¹ : ℂˣ) : ℂ) =
      ((archWeightCharAt hw n k⁻¹ : ℂˣ) : ℂ) *
        (((((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) ^ 2 - (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) ^ 2) -
          2 * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * s) := by
  set a := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((kr hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set uu : ℂ := ((archWeightOneAt hw k : ℂˣ) : ℂ) with huu
  have hu : uu = (a : ℂ) + (b : ℂ) * Complex.I := archWeightOneAt_mk hw k
  have hab : a ^ 2 + b ^ 2 = 1 := archWeightOneAt_normSq hw k
  have hinv1 : uu * ((a : ℂ) - (b : ℂ) * Complex.I) = 1 := by
    rw [hu]
    have : ((a : ℂ) + (b : ℂ) * Complex.I) * ((a : ℂ) - (b : ℂ) * Complex.I) = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this]; exact_mod_cast hab
  have hu0 : uu ≠ 0 := left_ne_zero_of_mul_eq_one hinv1
  have huinv : uu⁻¹ = (a : ℂ) - (b : ℂ) * Complex.I := inv_eq_of_mul_eq_one_right hinv1
  have hval : ((archWeightOneAt hw k⁻¹ : ℂˣ) : ℂ) = uu⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [archWeightCharAt_coe, archWeightCharAt_coe, hval, zpow_add₀ (inv_ne_zero hu0)]
  congr 1
  rcases hsσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [zpow_neg, zpow_ofNat, inv_pow, inv_inv, hu]
    ring_nf; rw [Complex.I_sq]; ring
  · rw [zpow_ofNat, huinv]
    ring_nf; rw [Complex.I_sq]; ring

private theorem continuous_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨_, hc, _⟩; exact hc
  · exact continuous_const
  · intro _ _ _ _ hu hv; exact hu.add hv
  · intro c _ _ hu; exact hu.const_smul c

section Engine

variable {H G : Type*} [Group H] [Group G]

private def Rt (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun x => f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem Rt_apply (g : G) (f : G → ℂ) (x : G) : Rt g f x = f (x * g) := rfl

private theorem Rt_mul (g g' : G) (f : G → ℂ) : Rt g (Rt g' f) = Rt (g * g') f := by
  funext x; simp [Rt_apply, mul_assoc]

private def RtStable (ι : H →* G) (E : Submodule ℂ (G → ℂ)) : Prop :=
  ∀ k : H, ∀ f ∈ E, Rt (ι k) f ∈ E

private theorem exists_fd_stable_of_mem_iSup {ι₀ : Type*} {W : ι₀ → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ι : H →* G) (ρ : ∀ i, Representation ℂ H (W i)) {f : G → ℂ}
    (hf : f ∈ ⨆ i, typeSubmodule ι (ρ i)) :
    ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ RtStable ι E ∧ f ∈ E := by

  have hP : ∀ i, ∀ f ∈ typeSubmodule ι (ρ i),
      ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ RtStable ι E ∧ f ∈ E := by
    intro i f hf
    refine Submodule.span_induction (p := fun f _ =>
      ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ RtStable ι E ∧ f ∈ E) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨T, hT, v, rfl⟩
      refine ⟨LinearMap.range T, inferInstance, fun k g hg => ?_, LinearMap.mem_range_self T v⟩
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hg
      refine LinearMap.mem_range.2 ⟨ρ i k u, funext fun x => ?_⟩
      rw [hT k u x]
      rfl
    · exact ⟨⊥, inferInstance, fun k g hg => by rw [(Submodule.mem_bot ℂ).1 hg]; exact Submodule.zero_mem _,
        Submodule.zero_mem _⟩
    · rintro f g - - ⟨E₁, hE₁, hs₁, hf₁⟩ ⟨E₂, hE₂, hs₂, hg₂⟩
      haveI := hE₁; haveI := hE₂
      refine ⟨E₁ ⊔ E₂, Submodule.finiteDimensional_sup E₁ E₂, fun k u hu => ?_,
        Submodule.add_mem_sup hf₁ hg₂⟩
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
      rw [map_add]
      exact Submodule.add_mem_sup (hs₁ k u₁ hu₁) (hs₂ k u₂ hu₂)
    · rintro c f - ⟨E, hE, hs, hfE⟩
      exact ⟨E, hE, hs, E.smul_mem c hfE⟩
  refine Submodule.iSup_induction _ (motive := fun f =>
    ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ RtStable ι E ∧ f ∈ E) hf hP ?_ ?_
  · exact ⟨⊥, inferInstance, fun k g hg => by rw [(Submodule.mem_bot ℂ).1 hg]; exact Submodule.zero_mem _,
      Submodule.zero_mem _⟩
  · rintro f g ⟨E₁, hE₁, hs₁, hf₁⟩ ⟨E₂, hE₂, hs₂, hg₂⟩
    haveI := hE₁; haveI := hE₂
    refine ⟨E₁ ⊔ E₂, Submodule.finiteDimensional_sup E₁ E₂, fun k u hu => ?_, Submodule.add_mem_sup hf₁ hg₂⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem_sup (hs₁ k u₁ hu₁) (hs₂ k u₂ hu₂)

private def trSpan (ι : H →* G) (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun k : H => Rt (ι k) f)

private theorem self_mem_trSpan (ι : H →* G) (f : G → ℂ) : f ∈ trSpan ι f := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext x; simp [Rt_apply]

private theorem trSpan_stable (ι : H →* G) (f : G → ℂ) : RtStable ι (trSpan ι f) := by
  intro k g hg
  refine Submodule.span_induction (p := fun g _ => Rt (ι k) g ∈ trSpan ι f) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨k', rfl⟩
    rw [Rt_mul, ← map_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  · show Rt (ι k) 0 ∈ trSpan ι f
    rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    show Rt (ι k) (a + b) ∈ trSpan ι f
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    show Rt (ι k) (c • a) ∈ trSpan ι f
    rw [map_smul]; exact Submodule.smul_mem _ c ha

private theorem trSpan_le_of_stable (ι : H →* G) {f : G → ℂ} {E : Submodule ℂ (G → ℂ)} (hs : RtStable ι E)
    (hf : f ∈ E) : trSpan ι f ≤ E :=
  Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hs k f hf)

private theorem trSpan_induction (ι : H →* G) (f : G → ℂ) {p : (G → ℂ) → Prop}
    (hgen : ∀ k : H, p (Rt (ι k) f)) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hsmul : ∀ (c : ℂ) a, p a → p (c • a)) {g : G → ℂ} (hg : g ∈ trSpan ι f) : p g := by
  refine Submodule.span_induction (p := fun g _ => p g) ?_ h0 (fun a b _ _ => hadd a b) (fun c a _ => hsmul c a) hg
  rintro _ ⟨k, rfl⟩; exact hgen k

private noncomputable def stableRep (ι : H →* G) (E : Submodule ℂ (G → ℂ)) (hs : RtStable ι E) :
    Representation ℂ H E :=
  Representation.subrepresentation
    ({ toFun := fun k => Rt (ι k)
       map_one' := by apply LinearMap.ext; intro f; funext x; simp [Rt_apply]
       map_mul' := fun a b => by apply LinearMap.ext; intro f; funext x; simp [Rt_apply, mul_assoc] } :
      Representation ℂ H (G → ℂ)) E (fun k f hf => hs k f hf)

private theorem stableRep_apply (ι : H →* G) (E : Submodule ℂ (G → ℂ)) (hs : RtStable ι E) (k : H) (u : E) :
    ((stableRep ι E hs k u : E) : G → ℂ) = Rt (ι k) (u : G → ℂ) := rfl

private theorem mem_typeSubmodule_of_equivariant_of_equiv (ι : H →* G)
    {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (σ : Representation ℂ H E) (σ' : Representation ℂ H E') (e : E ≃ₗ[ℂ] E')
    (he : ∀ (k : H) (u : E), e (σ k u) = σ' k (e u))
    (S : E →ₗ[ℂ] (G → ℂ)) (hS : ∀ (k : H) (u : E) (x : G), S (σ k u) x = S u (x * ι k)) (u : E) :
    S u ∈ typeSubmodule ι σ' := by
  have hT : IsRightEquivariant ι σ' (S ∘ₗ e.symm.toLinearMap) := by
    intro k v x
    show S (e.symm (σ' k v)) x = S (e.symm v) (x * ι k)
    have hv : σ' k v = e (σ k (e.symm v)) := by rw [he, LinearEquiv.apply_symm_apply]
    rw [hv, LinearEquiv.symm_apply_apply, hS]
  have hu : S u = (S ∘ₗ e.symm.toLinearMap) (e u) := by
    show S u = S (e.symm (e u)); rw [LinearEquiv.symm_apply_apply]
  rw [hu]
  exact mem_typeSubmodule_of_isRightEquivariant hT (e u)

private def conjRep {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (σ : Representation ℂ H E) (e : E ≃ₗ[ℂ] E') : Representation ℂ H E' where
  toFun k := e.toLinearMap ∘ₗ σ k ∘ₗ e.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext; intro v
    simp
  map_mul' a b := by
    apply LinearMap.ext; intro v
    simp

private theorem conjRep_apply {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (σ : Representation ℂ H E) (e : E ≃ₗ[ℂ] E') (k : H) (v : E') : conjRep σ e k v = e (σ k (e.symm v)) := rfl

private theorem conjRep_intertwines {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (σ : Representation ℂ H E) (e : E ≃ₗ[ℂ] E') (k : H) (u : E) : e (σ k u) = conjRep σ e k (e u) := by
  rw [conjRep_apply, LinearEquiv.symm_apply_apply]

private theorem exists_fin_rep_of_fd (ι : H →* G) {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (σ : Representation ℂ H E) :
    ∃ (n : ℕ) (π : Representation ℂ H (Fin n → ℂ)),
      ∀ (S : E →ₗ[ℂ] (G → ℂ)), (∀ (k : H) (u : E) (x : G), S (σ k u) x = S u (x * ι k)) →
        ∀ u : E, S u ∈ typeSubmodule ι π := by
  let e : E ≃ₗ[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := (Module.finBasis ℂ E).equivFun
  exact ⟨Module.finrank ℂ E, conjRep σ e, fun S hS u =>
    mem_typeSubmodule_of_equivariant_of_equiv ι σ (conjRep σ e) e (conjRep_intertwines σ e) S hS u⟩

private theorem exists_fin_rep_dual_of_fd (ι : H →* G) {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (σ : Representation ℂ H E) :
    ∃ (n : ℕ) (π : Representation ℂ H (Fin n → ℂ)),
      ∀ (S : E →ₗ[ℂ] (G → ℂ)), (∀ (k : H) (u : E) (x : G), S (σ k u) x = S u (x * ι k)) →
        ∀ u : E, S u ∈ typeSubmodule ι π.dual := by

  let e' : Module.Dual ℂ E ≃ₗ[ℂ] (Fin (Module.finrank ℂ (Module.Dual ℂ E)) → ℂ) :=
    (Module.finBasis ℂ (Module.Dual ℂ E)).equivFun
  let π : Representation ℂ H (Fin (Module.finrank ℂ (Module.Dual ℂ E)) → ℂ) := conjRep σ.dual e'
  refine ⟨_, π, fun S hS u => ?_⟩

  let ev : E ≃ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ E) := Module.evalEquiv ℂ E
  let d : Module.Dual ℂ (Module.Dual ℂ E) ≃ₗ[ℂ] Module.Dual ℂ (Fin (Module.finrank ℂ (Module.Dual ℂ E)) → ℂ) :=
    e'.symm.dualMap
  refine mem_typeSubmodule_of_equivariant_of_equiv ι σ π.dual (ev.trans d) (fun k v => ?_) S hS u

  apply LinearMap.ext
  intro x
  simp only [ev, d, π, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Module.evalEquiv_apply,
    Module.Dual.eval_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    conjRep_apply, LinearEquiv.symm_apply_apply, inv_inv]

end Engine

private theorem βs_comp_left (s : ℂ) {g₀ : AdelicGL2 (𝓞 K) K}
    (hcomm : ∀ (d : ArchDir) (t : ℝ), archFlowAt hw d t * g₀ = g₀ * archFlowAt hw d t)
    (γ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    βs hw s (fun z => γ (g₀ * z)) y = βs hw s γ (g₀ * y) := by
  have hL : ∀ d, Ld hw d (fun z => γ (g₀ * z)) y = Ld hw d γ (g₀ * y) := by
    intro d
    show deriv (fun t : ℝ => γ (g₀ * (archFlowAt hw d (-t) * y))) 0 = deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (g₀ * y))) 0
    congr 1
    funext t
    rw [← mul_assoc, ← hcomm, mul_assoc]
  simp only [βs, hL]

private theorem βs_comp_right (s : ℂ) (g₀ : AdelicGL2 (𝓞 K) K) (γ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    βs hw s (fun z => γ (z * g₀)) y = βs hw s γ (y * g₀) := by
  have hL : ∀ d, Ld hw d (fun z => γ (z * g₀)) y = Ld hw d γ (y * g₀) := by
    intro d
    show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y * g₀)) 0 = deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (y * g₀))) 0
    simp only [mul_assoc]
  simp only [βs, hL]

private theorem βs_add (s : ℂ) {γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ} {y : AdelicGL2 (𝓞 K) K}
    (h₁ : ∀ d : ArchDir, DifferentiableAt ℝ (fun t : ℝ => γ₁ (archFlowAt hw d (-t) * y)) 0)
    (h₂ : ∀ d : ArchDir, DifferentiableAt ℝ (fun t : ℝ => γ₂ (archFlowAt hw d (-t) * y)) 0) :
    βs hw s (fun z => γ₁ z + γ₂ z) y = βs hw s γ₁ y + βs hw s γ₂ y := by
  have hL : ∀ d, Ld hw d (fun z => γ₁ z + γ₂ z) y = Ld hw d γ₁ y + Ld hw d γ₂ y := by
    intro d
    show deriv (fun t : ℝ => γ₁ (archFlowAt hw d (-t) * y) + γ₂ (archFlowAt hw d (-t) * y)) 0 = _
    exact deriv_add (h₁ d) (h₂ d)
  simp only [βs, hL]
  ring

private theorem βs_smul (s c : ℂ) (γ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    βs hw s (fun z => c * γ z) y = c * βs hw s γ y := by
  have hL : ∀ d, Ld hw d (fun z => c * γ z) y = c * Ld hw d γ y := fun d => deriv_const_mul_field c
  simp only [βs, hL]
  ring

private theorem g5_differentiableAt_leftFlow {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (d : ArchDir) (z : AdelicGL2 (𝓞 K) K) :
    DifferentiableAt ℝ (fun t : ℝ => α (archFlowAt hw d (-t) * z)) 0 := by
  have h := g5_hasDerivAt_lift_curve hw hΦ hfa hα (g5_hasDerivAt_curve_neg d) (fun t => g5_curve_det d (-t)) z
  have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * z)) = fun t => α (archRealLiftAt hw (g5Curve d (-t)) * z) := by
    funext t; rw [g5_archFlowAt_eq_lift]
  rw [hfun]
  exact h.differentiableAt

private theorem left_piece {v : InfinitePlace K} (hvw : v ≠ w) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (s : ℂ)
    {c : ℕ} (τ : Fin c → ArchRepAt K v)
    (hmem : (fun x => α x⁻¹) ∈ ⨆ i, archTypeSubmoduleAt K v (τ i)) :
    ∃ (n : ℕ) (π : Representation ℂ (rowIsometrySubgroup₀ v.Completion) (Fin n → ℂ)),
      (fun x => βs hw s α x⁻¹) ∈ archTypeSubmoduleAt K v ⟨n, π⟩ := by
  set h : AdelicGL2 (𝓞 K) K → ℂ := fun x => α x⁻¹ with hh
  obtain ⟨E, hE, hEs, hhE⟩ := exists_fd_stable_of_mem_iSup (rowIsometryInclAt₀ K v) (fun i => (τ i).ρ) hmem
  haveI := hE
  haveI hfd : FiniteDimensional ℂ (trSpan (rowIsometryInclAt₀ K v) h) := Submodule.finiteDimensional_of_le (trSpan_le_of_stable (rowIsometryInclAt₀ K v) hEs hhE)

  have hdiff : ∀ u ∈ trSpan (rowIsometryInclAt₀ K v) h, ∀ (d : ArchDir) (y : AdelicGL2 (𝓞 K) K),
      DifferentiableAt ℝ (fun t : ℝ => u (archFlowAt hw d (-t) * y)⁻¹) 0 := by
    intro u hu d y
    refine trSpan_induction (rowIsometryInclAt₀ K v) h (p := fun u => DifferentiableAt ℝ (fun t : ℝ => u (archFlowAt hw d (-t) * y)⁻¹) 0)
      ?_ ?_ ?_ ?_ hu
    · intro k
      have hfun : (fun t : ℝ => Rt ((rowIsometryInclAt₀ K v) k) h (archFlowAt hw d (-t) * y)⁻¹) =
          fun t => α (archFlowAt hw d (-t) * ((rowIsometryInclAt₀ K v) k⁻¹ * y)) := by
        funext t
        show α ((archFlowAt hw d (-t) * y)⁻¹ * (rowIsometryInclAt₀ K v) k)⁻¹ = _
        rw [mul_inv_rev, inv_inv, ← map_inv, ← mul_assoc, ← archFlowAt_comm_of_ne hw hvw, mul_assoc]
      rw [hfun]
      exact g5_differentiableAt_leftFlow hw hΦ hfa hα d _
    · exact differentiableAt_const (0 : ℂ)
    · intro a b ha hb; exact ha.add hb
    · intro c' a ha; exact ha.const_smul c'

  let Φop : trSpan (rowIsometryInclAt₀ K v) h →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u => fun x => βs hw s (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) x⁻¹
      map_add' := fun u₁ u₂ => by
        funext x
        exact βs_add hw s (fun d => hdiff u₁ u₁.2 d x⁻¹) (fun d => hdiff u₂ u₂.2 d x⁻¹)
      map_smul' := fun c' u => by
        funext x
        exact βs_smul hw s c' (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) x⁻¹ }
  have hΦeq : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : trSpan (rowIsometryInclAt₀ K v) h) (x : AdelicGL2 (𝓞 K) K),
      Φop (stableRep (rowIsometryInclAt₀ K v) (trSpan (rowIsometryInclAt₀ K v) h) (trSpan_stable (rowIsometryInclAt₀ K v) h) k u) x = Φop u (x * (rowIsometryInclAt₀ K v) k) := by
    intro k u x
    show βs hw s (fun z => (Rt ((rowIsometryInclAt₀ K v) k) (u : AdelicGL2 (𝓞 K) K → ℂ)) z⁻¹) x⁻¹ =
      βs hw s (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) (x * (rowIsometryInclAt₀ K v) k)⁻¹
    have hfun : (fun z => (Rt ((rowIsometryInclAt₀ K v) k) (u : AdelicGL2 (𝓞 K) K → ℂ)) z⁻¹) =
        fun z => (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) ((rowIsometryInclAt₀ K v) k⁻¹ * z) := by
      funext z
      show (u : AdelicGL2 (𝓞 K) K → ℂ) (z⁻¹ * (rowIsometryInclAt₀ K v) k) = (u : AdelicGL2 (𝓞 K) K → ℂ) ((rowIsometryInclAt₀ K v) k⁻¹ * z)⁻¹
      rw [mul_inv_rev, map_inv, inv_inv]
    rw [hfun]
    refine (βs_comp_left hw s (fun d t => archFlowAt_comm_of_ne hw hvw k⁻¹ d t)
      (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) x⁻¹).trans ?_
    rw [mul_inv_rev, ← map_inv]
  obtain ⟨n, π, hπ⟩ := exists_fin_rep_of_fd (rowIsometryInclAt₀ K v) (stableRep (rowIsometryInclAt₀ K v) (trSpan (rowIsometryInclAt₀ K v) h) (trSpan_stable (rowIsometryInclAt₀ K v) h))
  refine ⟨n, π, ?_⟩
  have key := hπ Φop hΦeq ⟨h, self_mem_trSpan (rowIsometryInclAt₀ K v) h⟩
  have hh' : (fun z => h z⁻¹) = α := by funext z; simp [hh]
  change (fun x => βs hw s (fun z => h z⁻¹) x⁻¹) ∈ typeSubmodule (rowIsometryInclAt₀ K v) π at key
  rw [hh'] at key
  exact key

private theorem right_piece {v : InfinitePlace K} {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : g5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (s : ℂ)
    {c : ℕ} (τ : Fin c → ArchRepAt K v)
    (hmem : α ∈ ⨆ i, archDualTypeSubmoduleAt K v (τ i)) :
    ∃ (n : ℕ) (π : Representation ℂ (rowIsometrySubgroup₀ v.Completion) (Fin n → ℂ)),
      βs hw s α ∈ archDualTypeSubmoduleAt K v ⟨n, π⟩ := by
  obtain ⟨E, hE, hEs, hαE⟩ := exists_fd_stable_of_mem_iSup (rowIsometryInclAt₀ K v) (fun i => (τ i).ρ.dual) hmem
  haveI := hE
  haveI hfd : FiniteDimensional ℂ (trSpan (rowIsometryInclAt₀ K v) α) := Submodule.finiteDimensional_of_le (trSpan_le_of_stable (rowIsometryInclAt₀ K v) hEs hαE)
  have hdiff : ∀ u ∈ trSpan (rowIsometryInclAt₀ K v) α, ∀ (d : ArchDir) (y : AdelicGL2 (𝓞 K) K),
      DifferentiableAt ℝ (fun t : ℝ => u (archFlowAt hw d (-t) * y)) 0 := by
    intro u hu d y
    refine trSpan_induction (rowIsometryInclAt₀ K v) α (p := fun u => DifferentiableAt ℝ (fun t : ℝ => u (archFlowAt hw d (-t) * y)) 0)
      ?_ ?_ ?_ ?_ hu
    · intro k
      have hfun : (fun t : ℝ => Rt ((rowIsometryInclAt₀ K v) k) α (archFlowAt hw d (-t) * y)) = fun t => α (archFlowAt hw d (-t) * (y * (rowIsometryInclAt₀ K v) k)) := by
        funext t
        show α (archFlowAt hw d (-t) * y * (rowIsometryInclAt₀ K v) k) = _
        rw [mul_assoc]
      rw [hfun]
      exact g5_differentiableAt_leftFlow hw hΦ hfa hα d _
    · exact differentiableAt_const (0 : ℂ)
    · intro a b ha hb; exact ha.add hb
    · intro c' a ha; exact ha.const_smul c'
  let Φop : trSpan (rowIsometryInclAt₀ K v) α →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u => βs hw s (u : AdelicGL2 (𝓞 K) K → ℂ)
      map_add' := fun u₁ u₂ => by
        funext x
        exact βs_add hw s (fun d => hdiff u₁ u₁.2 d x) (fun d => hdiff u₂ u₂.2 d x)
      map_smul' := fun c' u => by
        funext x
        exact βs_smul hw s c' (u : AdelicGL2 (𝓞 K) K → ℂ) x }
  have hΦeq : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : trSpan (rowIsometryInclAt₀ K v) α) (x : AdelicGL2 (𝓞 K) K),
      Φop (stableRep (rowIsometryInclAt₀ K v) (trSpan (rowIsometryInclAt₀ K v) α) (trSpan_stable (rowIsometryInclAt₀ K v) α) k u) x = Φop u (x * (rowIsometryInclAt₀ K v) k) := by
    intro k u x
    exact βs_comp_right hw s ((rowIsometryInclAt₀ K v) k) (u : AdelicGL2 (𝓞 K) K → ℂ) x
  obtain ⟨n, π, hπ⟩ := exists_fin_rep_dual_of_fd (rowIsometryInclAt₀ K v) (stableRep (rowIsometryInclAt₀ K v) (trSpan (rowIsometryInclAt₀ K v) α) (trSpan_stable (rowIsometryInclAt₀ K v) α))
  exact ⟨n, π, hπ Φop hΦeq ⟨α, self_mem_trSpan (rowIsometryInclAt₀ K v) α⟩⟩

private def refineFam (tys : ArchTypeFamily K) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ) :
    ArchTypeFamily K :=
  ⟨tys.card, fun v i => if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i⟩

private theorem mem_archCutSubmodule_refineFam {tys : ArchTypeFamily K}
    {χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) (hχ : ∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χ v) φ) :
    φ ∈ archCutSubmodule K (refineFam tys χ) := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro v
  show φ ∈ ⨆ i : Fin (tys.card v), archTypeSubmoduleAt K v (if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i)
  by_cases hv : v.IsReal
  · simp only [if_pos hv]
    rcases Nat.eq_zero_or_pos (tys.card v) with h0 | hpos
    · have hφ0 : φ = 0 := by
        have h := hφ v
        haveI : IsEmpty (Fin (tys.card v)) := ⟨fun i => absurd i.2 (by omega)⟩
        rwa [iSup_of_empty, Submodule.mem_bot] at h
      rw [hφ0]
      exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem (⟨0, hpos⟩ : Fin (tys.card v))
        ((mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) φ).mpr (hχ v hv))
  · simp only [if_neg hv]
    exact hφ v

private theorem laws_of_refineFam {tys : ArchTypeFamily K}
    {χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ} {α : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsArchBiFinite K (refineFam tys χ) α) (v : InfinitePlace K) (hv : v.IsReal) :
    (∀ (k : rowIsometrySubgroup₀ v.Completion) (z : AdelicGL2 (𝓞 K) K),
        α (rowIsometryInclAt₀ K v k * z) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α z) ∧
    (∀ (k : rowIsometrySubgroup₀ v.Completion) (g : AdelicGL2 (𝓞 K) K),
        α (g * rowIsometryInclAt₀ K v k) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α g) := by
  have h1 := (mem_archCutSubmodule_iff K _ _).1 h.1 v
  have h2 := (mem_archDualCutSubmodule_iff K _ _).1 h.2 v
  change (fun x => α x⁻¹) ∈ ⨆ i : Fin (tys.card v),
    archTypeSubmoduleAt K v (if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i) at h1
  change α ∈ ⨆ i : Fin (tys.card v),
    archDualTypeSubmoduleAt K v (if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i) at h2
  simp only [if_pos hv] at h1 h2
  have hle1 : (⨆ _ : Fin (tys.card v), archTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v))) ≤
      archTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v)) := iSup_le fun _ => le_rfl
  have hle2 : (⨆ _ : Fin (tys.card v), archDualTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v))) ≤
      archDualTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ v)) := iSup_le fun _ => le_rfl
  exact ⟨(comp_inv_mem_archTypeSubmoduleAt_ofChar_iff K v (χ v) α).mp (hle1 h1),
    (mem_archDualTypeSubmoduleAt_ofChar_iff K v (χ v) α).mp (hle2 h2)⟩

private theorem complex_mem_of_refineFam {tys : ArchTypeFamily K}
    {χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ} {α : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsArchBiFinite K (refineFam tys χ) α) (v : InfinitePlace K) (hv : ¬ v.IsReal) :
    (fun x => α x⁻¹) ∈ ⨆ i : Fin (tys.card v), archTypeSubmoduleAt K v (tys.rep v i) ∧
    α ∈ ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt K v (tys.rep v i) := by
  have h1 := (mem_archCutSubmodule_iff K _ _).1 h.1 v
  have h2 := (mem_archDualCutSubmodule_iff K _ _).1 h.2 v
  change (fun x => α x⁻¹) ∈ ⨆ i : Fin (tys.card v),
    archTypeSubmoduleAt K v (if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i) at h1
  change α ∈ ⨆ i : Fin (tys.card v),
    archDualTypeSubmoduleAt K v (if v.IsReal then ArchRepAt.ofChar K (χ v) else tys.rep v i) at h2
  simp only [if_neg hv] at h1 h2
  exact ⟨h1, h2⟩

private def mixFam (χa χb : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (τ₁ τ₂ : ∀ v : InfinitePlace K, ¬ v.IsReal → ArchRepAt K v) : ArchTypeFamily K :=
  ⟨fun _ => 2, fun v => if hv : v.IsReal then ![ArchRepAt.ofChar K (χa v), ArchRepAt.ofChar K (χb v)]
    else ![τ₁ v hv, τ₂ v hv]⟩

private theorem step_gen (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : ArchTypeFamily K)
    (χ χ' : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ) (n σ : ℤ) (s : ℂ)
    (hsσ : (s = -Complex.I ∧ σ = -2) ∨ (s = Complex.I ∧ σ = 2))
    (hχw : χ w = archWeightCharAt hw n) (hχ' : ∀ v : InfinitePlace K, v ≠ w → χ' v = χ v)
    (hχ'w : χ' w = archWeightCharAt hw (n + σ))
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hyχ : ∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χ v) y) :
    (∃ tys' : ArchTypeFamily K,
      archDerivAt hw .H y + s • (archDerivAt hw .E y + archDerivAt hw .Fm y) ∈
        V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
    ∀ v : InfinitePlace K, v.IsReal →
      HasArchCharacterAt₀ K v (χ' v) (archDerivAt hw .H y + s • (archDerivAt hw .E y + archDerivAt hw .Fm y)) := by
  have hs2 : s ^ 2 = -1 := by
    rcases hsσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [neg_sq, Complex.I_sq]
    · exact Complex.I_sq

  have hyR : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (refineFam tys χ) :=
    ⟨hy.1, mem_archCutSubmodule_refineFam hy.2 hyχ⟩
  obtain ⟨y', hy', α, hαf, hαb, hαU, hyeq⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN
      (refineFam tys χ) y hyR
  have hy'V : y' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy').1).1
  have hy'c : Continuous y' := continuous_of_mem_cuspKFiniteSubmodule (hV.1.le hy'V)
  obtain ⟨fa, ff, hfaT, hff, hαeq⟩ := hαf
  obtain ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩ := hfaT
  have hαf' : IsFactorizableTestFn K α := ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩

  have hD : ∀ d, archDerivAt hw d y = rightConv K y' (Ld hw d α) := fun d => by
    rw [hyeq]
    exact ((AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 y' α hy'c hαf').2

  have hT : ∀ d, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
      ∀ z, Ld hw d α z = fa' (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z) := by
    intro d
    obtain ⟨fa', hfa', heq⟩ :=
      (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩
    refine ⟨fa', hfa', fun z => ?_⟩
    have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * z)) =
        fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * z)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * z)) := by
      funext t; exact hαeq _
    show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * z)) 0 = _
    rw [hfun]
    exact congrFun heq z
  obtain ⟨faH, ⟨⟨ΦH, hΦH, hfaH⟩, hsH⟩, hH⟩ := hT .H
  obtain ⟨faE, ⟨⟨ΦE, hΦE, hfaE⟩, hsE⟩, hE⟩ := hT .E
  obtain ⟨faF, ⟨⟨ΦF, hΦF, hfaF⟩, hsF⟩, hF⟩ := hT .Fm
  have hfac : ∀ d, IsFactorizableTestFn K (Ld hw d α) := fun d => by
    obtain ⟨fa', hfa', heq⟩ := hT d; exact ⟨fa', ff, hfa', hff, heq⟩

  set β : AdelicGL2 (𝓞 K) K → ℂ := βs hw s α with hβ
  have hβeq : ∀ z, β z = (fun x => faH x + s * (faE x + faF x)) (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z) := by
    intro z
    show Ld hw .H α z + s * (Ld hw .E α z + Ld hw .Fm α z) = _
    rw [hH, hE, hF]; ring
  have hβf : IsFactorizableTestFn K β := by
    refine ⟨fun x => faH x + s * (faE x + faF x), ff, ⟨⟨fun m => ΦH m + s * (ΦE m + ΦF m), ?_, fun x => ?_⟩, ?_⟩, hff, hβeq⟩
    · exact hΦH.add (contDiff_const.mul (hΦE.add hΦF))
    · show faH x + s * (faE x + faF x) = _; rw [hfaH, hfaE, hfaF]
    · exact hsH.add (hsE.add hsF).mul_left

  have hop : archDerivAt hw .H y + s • (archDerivAt hw .E y + archDerivAt hw .Fm y) = rightConv K y' β := by
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
    haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
    have hint : ∀ d (g : AdelicGL2 (𝓞 K) K), Integrable (fun z => y' (g * z) * Ld hw d α z) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro d g
      obtain ⟨hc', hs'⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hfac d)
      exact ((hy'c.comp (continuous_const.mul continuous_id)).mul hc').integrable_of_hasCompactSupport hs'.mul_left
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD]
    rw [rightConv_apply, rightConv_apply, rightConv_apply, rightConv_apply]
    have hfun : (fun z => y' (g * z) * β z) = fun z => y' (g * z) * Ld hw .H α z + s * (y' (g * z) * Ld hw .E α z + y' (g * z) * Ld hw .Fm α z) := by
      funext z
      show y' (g * z) * (Ld hw .H α z + s * (Ld hw .E α z + Ld hw .Fm α z)) = _
      ring
    have hEF : Integrable (fun z => y' (g * z) * Ld hw .E α z + y' (g * z) * Ld hw .Fm α z)
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := (hint .E g).add (hint .Fm g)
    have hB : Integrable (fun z => s * (y' (g * z) * Ld hw .E α z + y' (g * z) * Ld hw .Fm α z))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := hEF.const_mul s
    rw [hfun, integral_add (hint .H g) hB, integral_const_mul, integral_add (hint .E g) (hint .Fm g)]

  have hαL : ∀ (v : InfinitePlace K), v.IsReal → ∀ (k : rowIsometrySubgroup₀ v.Completion) (z : AdelicGL2 (𝓞 K) K),
      α (rowIsometryInclAt₀ K v k * z) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α z := fun v hv => (laws_of_refineFam (h := hαb) v hv).1
  have hαR : ∀ (v : InfinitePlace K), v.IsReal → ∀ (k : rowIsometrySubgroup₀ v.Completion) (g : AdelicGL2 (𝓞 K) K),
      α (g * rowIsometryInclAt₀ K v k) = ((χ v k⁻¹ : ℂˣ) : ℂ) * α g := fun v hv => (laws_of_refineFam (h := hαb) v hv).2

  have hβR : ∀ (v : InfinitePlace K), v.IsReal → ∀ (k : rowIsometrySubgroup₀ v.Completion) (g : AdelicGL2 (𝓞 K) K),
      β (g * rowIsometryInclAt₀ K v k) = ((χ v k⁻¹ : ℂˣ) : ℂ) * β g := fun v hv k g => βs_right_law hw s (hαR v hv k) g
  have hβL : ∀ (v : InfinitePlace K), v.IsReal → ∀ (k : rowIsometrySubgroup₀ v.Completion) (z : AdelicGL2 (𝓞 K) K),
      β (rowIsometryInclAt₀ K v k * z) = ((χ' v k⁻¹ : ℂˣ) : ℂ) * β z := by
    intro v hv k z
    by_cases hvw : v = w
    · subst hvw
      rw [hβ, βs_left_w hw hΦ hfa hαeq (hαL v hv) hs2 k z, hχ'w, hχw, weight_shift hw n σ s hsσ k]
    · rw [hχ' v hvw]
      exact βs_left_law hw s (archFlowAt_comm_of_ne hw hvw k) (hαL v hv k) z
  have hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ z : AdelicGL2 (𝓞 K) K, β (k * z) = β z := by
    intro k hk z
    have hk1 : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2
    have h := βs_left_law hw s (archFlowAt_comm_of_glArch hw hk1) (cc := 1) (fun z => by rw [one_mul]; exact (hαU z k hk).1) z
    rwa [one_mul] at h

  have hCL : ∀ (v : InfinitePlace K) (hv : ¬ v.IsReal), ∃ (nn : ℕ) (π : Representation ℂ (rowIsometrySubgroup₀ v.Completion) (Fin nn → ℂ)),
      (fun x => β x⁻¹) ∈ archTypeSubmoduleAt K v ⟨nn, π⟩ := by
    intro v hv
    have hvw : v ≠ w := fun h => hv (h ▸ hw)
    exact left_piece hw hvw hΦ hfa hαeq s (tys.rep v) (complex_mem_of_refineFam hαb v hv).1
  have hCR : ∀ (v : InfinitePlace K) (hv : ¬ v.IsReal), ∃ (nn : ℕ) (π : Representation ℂ (rowIsometrySubgroup₀ v.Completion) (Fin nn → ℂ)),
      β ∈ archDualTypeSubmoduleAt K v ⟨nn, π⟩ := by
    intro v hv
    exact right_piece hw hΦ hfa hαeq s (tys.rep v) (complex_mem_of_refineFam hαb v hv).2
  choose n₁ π₁ hπ₁ using hCL
  choose n₂ π₂ hπ₂ using hCR

  let tysβ : ArchTypeFamily K := mixFam χ' χ (fun v hv => ⟨n₁ v hv, π₁ v hv⟩) (fun v hv => ⟨n₂ v hv, π₂ v hv⟩)
  have hβLmem : ∀ (v : InfinitePlace K), v.IsReal → (fun x => β x⁻¹) ∈ archTypeSubmoduleAt K v (ArchRepAt.ofChar K (χ' v)) :=
    fun v hv => (comp_inv_mem_archTypeSubmoduleAt_ofChar_iff K v (χ' v) β).mpr (hβL v hv)
  have hβb : IsArchBiFinite K tysβ β := by
    refine ⟨(mem_archCutSubmodule_iff K tysβ _).mpr fun v => ?_, (mem_archDualCutSubmodule_iff K tysβ _).mpr fun v => ?_⟩
    · show (fun x => β x⁻¹) ∈ ⨆ i : Fin 2, archTypeSubmoduleAt K v
        ((if hv : v.IsReal then ![ArchRepAt.ofChar K (χ' v), ArchRepAt.ofChar K (χ v)]
          else ![(⟨n₁ v hv, π₁ v hv⟩ : ArchRepAt K v), ⟨n₂ v hv, π₂ v hv⟩]) i)
      by_cases hv : v.IsReal
      · rw [dif_pos hv]
        exact Submodule.mem_iSup_of_mem (0 : Fin 2) (by simpa using hβLmem v hv)
      · rw [dif_neg hv]
        exact Submodule.mem_iSup_of_mem (0 : Fin 2) (by simpa using hπ₁ v hv)
    · show β ∈ ⨆ i : Fin 2, archDualTypeSubmoduleAt K v
        ((if hv : v.IsReal then ![ArchRepAt.ofChar K (χ' v), ArchRepAt.ofChar K (χ v)]
          else ![(⟨n₁ v hv, π₁ v hv⟩ : ArchRepAt K v), ⟨n₂ v hv, π₂ v hv⟩]) i)
      by_cases hv : v.IsReal
      · rw [dif_pos hv]
        exact Submodule.mem_iSup_of_mem (1 : Fin 2)
          (by simpa using (mem_archDualTypeSubmoduleAt_ofChar_iff K v (χ v) β).mpr (hβR v hv))
      · rw [dif_neg hv]
        exact Submodule.mem_iSup_of_mem (1 : Fin 2) (by simpa using hπ₂ v hv)

  rw [hop]
  have hmemV : rightConv K y' β ∈ V := hV.1.rightConv_mem β tysβ hβf hβb y' hy'V
  have hlev : rightConv K y' β ∈ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N := by
    intro g k hk
    rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    have hfun : (fun z => β (k⁻¹ * z)) = β := funext fun z => hβU k⁻¹ (Subgroup.inv_mem _ hk) z
    rw [hfun]
  refine ⟨⟨tysβ, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hmemV, hlev⟩,
    AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tysβ y' hy'c β hβf hβb⟩⟩, fun v hv => ?_⟩
  exact hasArchCharacterAt₀_rightConv K v (χ' v) y' β (hβL v hv)

end Step

end GStab

end

open GStab in
set_option linter.unusedVariables false in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (lower^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2 * j)) (lower^[j] y)) ∧
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (raise^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2 * j)) (raise^[j] y)) := by
  intro lower raise
  classical
  choose nv hnv using hpure

  let χf : ℤ → ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
    fun m v => if hv : v.IsReal then archWeightCharAt hv (if v = w then m else nv v hv) else 1
  have hχf_w : ∀ m : ℤ, χf m w = archWeightCharAt hw m := by
    intro m
    show (if hv : w.IsReal then archWeightCharAt hv (if w = w then m else nv w hv) else 1) = archWeightCharAt hw m
    rw [dif_pos hw, if_pos rfl]
  have hχf_ne : ∀ (m m' : ℤ) (v : InfinitePlace K), v ≠ w → χf m v = χf m' v := by
    intro m m' v hv; simp only [χf, if_neg hv]
  have hχf_real : ∀ (m : ℤ) (v : InfinitePlace K) (hv : v.IsReal), v ≠ w → χf m v = archWeightCharAt hv (nv v hv) := by
    intro m v hv hvw; simp only [χf, dif_pos hv, if_neg hvw]

  have base : ∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χf n v) y := by
    intro v hv
    by_cases hvw : v = w
    · subst hvw; rw [hχf_w]; exact hyn
    · rw [hχf_real n v hv hvw]; exact hnv v hv
  have hlow : ∀ x : AdelicGL2 (𝓞 K) K → ℂ, lower x =
      archDerivAt hw .H x + (-Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x) := fun x => by
    show archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) = _
    rw [sub_eq_add_neg, neg_smul]

  have iterL : ∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      ∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χf (n - 2 * j) v) (lower^[j] y) := by
    intro j
    induction j with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, sub_zero]
      exact ⟨⟨tys, hy⟩, base⟩
    | succ j ih =>
      obtain ⟨⟨tysj, hyj⟩, hχj⟩ := ih
      rw [Function.iterate_succ_apply', hlow]
      exact GStab.step_gen hw c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tysj (χf (n - 2 * (j : ℤ)))
        (χf (n - 2 * ((j + 1 : ℕ) : ℤ))) (n - 2 * (j : ℤ)) (-2) (-Complex.I) (Or.inl ⟨rfl, rfl⟩) (hχf_w _)
        (fun v hv => hχf_ne _ _ v hv) (by rw [hχf_w]; congr 1; push_cast; ring) _ hyj hχj
  have iterR : ∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      ∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χf (n + 2 * j) v) (raise^[j] y) := by
    intro j
    induction j with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero]
      exact ⟨⟨tys, hy⟩, base⟩
    | succ j ih =>
      obtain ⟨⟨tysj, hyj⟩, hχj⟩ := ih
      rw [Function.iterate_succ_apply']
      exact GStab.step_gen hw c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tysj (χf (n + 2 * (j : ℤ)))
        (χf (n + 2 * ((j + 1 : ℕ) : ℤ))) (n + 2 * (j : ℤ)) 2 Complex.I (Or.inr ⟨rfl, rfl⟩) (hχf_w _)
        (fun v hv => hχf_ne _ _ v hv) (by rw [hχf_w]; congr 1; push_cast; ring) _ hyj hχj

  have hzero : ∀ op : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ),
      (∀ x, op x = archDerivAt hw .H x + (-Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x)) ∨
      (∀ x, op x = archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)) →
      ∀ j : ℕ, op^[j] (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
    intro op hop j
    have hD0 : ∀ d, archDerivAt hw d (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
      intro d; funext g; show deriv (fun t : ℝ => (0 : AdelicGL2 (𝓞 K) K → ℂ) (g * archFlowAt hw d t)) 0 = 0
      exact deriv_const 0 0
    have h1 : op 0 = 0 := by
      rcases hop with h | h <;> rw [h, hD0, hD0, hD0] <;> simp
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, h1]
  have transfer : ∀ (z : AdelicGL2 (𝓞 K) K → ℂ) (m₀ : ℤ), (y = 0 → z = 0) →
      (∀ v : InfinitePlace K, v.IsReal → HasArchCharacterAt₀ K v (χf m₀ v) z) →
      ∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) z := by
    intro z m₀ hz hχz v hv m hvw hm
    by_cases hy0 : y = 0
    · rw [hz hy0]; intro k g; simp
    · obtain ⟨g₁, hg₁⟩ : ∃ g, y g ≠ 0 := by
        by_contra h
        push Not at h
        exact hy0 (funext h)
      have heq : archWeightCharAt hv m = archWeightCharAt hv (nv v hv) := by
        apply MonoidHom.ext
        intro k
        apply Units.ext
        have h1 := hm k g₁
        have h2 := hnv v hv k g₁
        rw [h1] at h2
        exact mul_right_cancel₀ hg₁ h2
      have h := hχz v hv
      rw [hχf_real m₀ v hv hvw] at h
      rw [heq]; exact h
  refine ⟨fun j => ⟨(iterL j).1, transfer _ _ (fun h0 => by subst h0; exact hzero lower (Or.inl hlow) j) (iterL j).2, ?_⟩,
    fun j => ⟨(iterR j).1, transfer _ _ (fun h0 => by subst h0; exact hzero raise (Or.inr fun x => rfl) j) (iterR j).2, ?_⟩⟩
  · have h := (iterL j).2 w hw; rwa [hχf_w] at h
  · have h := (iterR j).2 w hw; rwa [hχf_w] at h

end S_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt (solution)
