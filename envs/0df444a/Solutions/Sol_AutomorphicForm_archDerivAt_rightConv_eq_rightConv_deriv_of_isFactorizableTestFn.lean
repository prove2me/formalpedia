-- Prove2me | solution 1 for AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/08ece951-dddc-5ddd-810c-ef51050238db

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.Deriv.Mul
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
set_option autoImplicit false

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

noncomputable section

private abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

private abbrev tcDetSet : Set Ent := {e : Ent | (Matrix.of e).det ≠ 0}

private theorem tc_isOpen_detSet : IsOpen tcDetSet := by
  have h : Continuous fun e : Ent => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

section LiftAnalysis

private def tcInv (e : Ent) : Ent := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

private theorem tc_of_tcInv {e : Ent} : Matrix.of (tcInv e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [tcInv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

private theorem tc_det_tcInv {e : Ent} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (tcInv e)).det ≠ 0 := by
  rw [tc_of_tcInv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem tc_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i).contDiff

private theorem tc_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((tc_contDiff_entry 0 0).mul (tc_contDiff_entry 1 1)).sub ((tc_contDiff_entry 0 1).mul (tc_contDiff_entry 1 0))

private theorem tc_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Ent => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact tc_contDiff_entry _ _ | exact (tc_contDiff_entry _ _).neg

private theorem tc_contDiffOn_tcInv : ContDiffOn ℝ (⊤ : ℕ∞) tcInv tcDetSet :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    (tc_contDiff_adj i j).contDiffOn.div tc_contDiff_det.contDiffOn fun _ he => he

private theorem tc_tcInv_mem {e : Ent} (he : e ∈ tcDetSet) : tcInv e ∈ tcDetSet := tc_det_tcInv he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem l5_lift_inv (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archRealLiftAt hw (tcInv e) := by
  rw [archRealLiftAt_of_det_ne_zero hw he, archRealLiftAt_of_det_ne_zero hw (tc_det_tcInv he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact tc_of_tcInv.symm

private def l5Theta (hw : w.IsReal) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (archMatrixUpdate K w (A.map (ringEquivRealOfIsReal hw).symm) i j,
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j)

private theorem l5_coe_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ((archRealGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      l5Theta hw (m : Matrix (Fin 2) (Fin 2) ℝ) :=
  rfl

private theorem l5_continuous_Theta (hw : w.IsReal) : Continuous (l5Theta (K := K) hw) := by
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

private theorem l5_continuousOn_lift (hw : w.IsReal) :
    ContinuousOn (fun e : Ent => (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)) tcDetSet := by
  rw [continuousOn_iff_continuous_restrict]
  have hdet : ∀ e : tcDetSet, (Matrix.of (e : Ent)).det ≠ 0 := fun e => e.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : tcDetSet,
        ((archRealLiftAt hw (e : Ent) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          l5Theta hw (Matrix.of (e : Ent)) := fun e => by
      rw [archRealLiftAt_of_det_ne_zero hw (hdet e), l5_coe_archRealGLAt]
      rfl
    exact ((l5_continuous_Theta hw).comp continuous_subtype_val).congr fun e => (h e).symm
  · have h : ∀ e : tcDetSet,
        (((archRealLiftAt hw (e : Ent) : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = l5Theta hw (Matrix.of (tcInv (e : Ent))) := fun e => by
      rw [l5_lift_inv hw (hdet e), archRealLiftAt_of_det_ne_zero hw (tc_det_tcInv (hdet e)), l5_coe_archRealGLAt]
      rfl
    exact ((l5_continuous_Theta hw).comp
      (continuousOn_iff_continuous_restrict.1 tc_contDiffOn_tcInv.continuousOn)).congr fun e => (h e).symm

end LiftAnalysis

section AffineData

open scoped Classical

section FieldOnly

variable (K : Type) [Field K]

private abbrev l5Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private theorem l5_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem l5_continuous_archEntries : Continuous (archEntries K) := by
  have hval : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      (a.val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => (l5_continuous_ringEquiv K).comp ?_
  exact (continuous_apply j).comp
    ((continuous_apply i : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m i).comp hval)

private theorem l5_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

private theorem l5_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  l5_archEntries_eq_mapMatrix K g

private theorem l5_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [l5_of_archEntries, Units.val_mul, map_mul]

variable {K}

private def l5single (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

private theorem l5_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) :
    archMatrixUpdate K w m i j = archMatrixUpdate K w 0 i j + l5single w (m i j) := by
  funext v
  show archMatrixUpdate K w m i j v =
    archMatrixUpdate K w 0 i j v + Pi.single (M := fun v : InfinitePlace K => v.Completion) w (m i j) v
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self, archMatrixUpdate_apply_self, Pi.single_eq_same, Matrix.zero_apply, zero_add]
  · rw [archMatrixUpdate_apply_of_ne K w m i j hv, archMatrixUpdate_apply_of_ne K w 0 i j hv, Pi.single_eq_of_ne hv,
      add_zero]

private def l5Const (w : InfinitePlace K) : l5Ent K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

private theorem l5_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      l5Const w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (l5single w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [l5_archMatrixUpdate_entry, map_add]
  rfl

private def l5AddHom {w : InfinitePlace K} (hw : w.IsReal) : ℝ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivRealOfIsReal hw).symm.toAddMonoidHom)

private theorem l5AddHom_apply {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    l5AddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (l5single w ((ringEquivRealOfIsReal hw).symm r)) :=
  rfl

private theorem l5_continuous_addHom {w : InfinitePlace K} (hw : w.IsReal) : Continuous (l5AddHom hw) := by
  have h1 : Continuous fun x : w.Completion => l5single w x := continuous_single w
  have h2 : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  have h3 : ⇑(l5AddHom hw) = fun r : ℝ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (l5single w ((ringEquivRealOfIsReal hw).symm r)) :=
    funext fun r => l5AddHom_apply hw r
  rw [h3]
  exact (l5_continuous_ringEquiv K).comp (h1.comp h2)

private def l5Lin {w : InfinitePlace K} (hw : w.IsReal) : ℝ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (l5AddHom hw).toRealLinearMap (l5_continuous_addHom hw)

private def l5LinMat {w : InfinitePlace K} (hw : w.IsReal) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] l5Ent K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (l5Lin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

private theorem l5LinMat_apply {w : InfinitePlace K} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    l5LinMat hw e i j = l5AddHom hw (e i j) :=
  rfl

end FieldOnly

section NumberFieldPart

variable {K : Type} [Field K] [NumberField K]

private theorem l5_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e)) = l5Const w + l5LinMat hw e := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  have h1 : glArch (𝓞 K) K (archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) :=
    glArch_adelicArchGLIncl K _
  rw [h1]
  funext i j
  rw [l5_archEntries_archGLIncl, glEquivOfRingEquiv_apply_entry, Pi.add_apply, Pi.add_apply, l5LinMat_apply,
    l5AddHom_apply]
  rfl

end NumberFieldPart

end AffineData

section TestData

open MeasureTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem l5_glFin_lift (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archRealLiftAt hw e) = 1 := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

private theorem l5_glFin_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 K) K (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl K _

private def l5MulRLin (M : l5Ent K) : l5Ent K →ₗ[ℝ] l5Ent K where
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

private def l5MulR (M : l5Ent K) : l5Ent K →L[ℝ] l5Ent K := LinearMap.toContinuousLinearMap (l5MulRLin M)

private theorem l5MulR_apply (M N : l5Ent K) : l5MulR M N = Matrix.of.symm (Matrix.of N * Matrix.of M) := rfl

private def l5MulRL : l5Ent K →ₗ[ℝ] (l5Ent K →L[ℝ] l5Ent K) where
  toFun := l5MulR
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

private theorem l5_continuous_mulR : Continuous (l5MulR : l5Ent K → l5Ent K →L[ℝ] l5Ent K) :=
  (l5MulRL (K := K)).continuous_of_finiteDimensional

private def l5MulLLin (A : l5Ent K) : l5Ent K →ₗ[ℝ] l5Ent K where
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

private def l5MulL (A : l5Ent K) : l5Ent K →L[ℝ] l5Ent K := LinearMap.toContinuousLinearMap (l5MulLLin A)

private theorem l5MulL_apply (A N : l5Ent K) : l5MulL A N = Matrix.of.symm (Matrix.of A * Matrix.of N) := rfl

private theorem l5_archEntries_lift_mul (hw : w.IsReal) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y)) =
      l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5Const w) +
        l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5LinMat hw e) := by
  rw [l5MulR_apply, l5MulR_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y))), map_mul,
    l5_archEntries_mul, l5_archEntries_glArch_lift hw he]
  show Matrix.of.symm ((Matrix.of (l5Const w) + Matrix.of (l5LinMat hw e)) *
    Matrix.of (archEntries K (glArch (𝓞 K) K y))) = _
  rw [Matrix.add_mul]
  rfl

private theorem l5_factor_lift_mul (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : l5Ent K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (archRealLiftAt hw e * y) =
      Φ (l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5Const w) +
          l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5LinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, l5_archEntries_lift_mul hw he, map_mul, l5_glFin_lift hw he, one_mul]

open scoped Classical in

private theorem l5_isFactorizableTestFn_archRealGLAt_mul (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K fun y => α (archRealGLAt hw m * y) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hfa_supp⟩, hff, hαeq⟩ := hα
  refine ⟨fun z => fa (glArch (𝓞 K) K (archRealGLAt hw m) * z), ff,
    ⟨⟨fun N => Φ (l5MulL (archEntries K (glArch (𝓞 K) K (archRealGLAt hw m))) N), ?_, ?_⟩, ?_⟩, hff, ?_⟩
  · exact hΦ.comp (l5MulL (archEntries K (glArch (𝓞 K) K (archRealGLAt hw m)))).contDiff
  · intro z
    beta_reduce
    rw [hfa, l5MulL_apply]
    congr 1
    rw [← l5_archEntries_mul]
    exact (Matrix.of.symm_apply_apply _).symm
  · exact hfa_supp.comp_homeomorph (Homeomorph.mulLeft (glArch (𝓞 K) K (archRealGLAt hw m)))
  · intro y
    beta_reduce
    rw [hαeq, map_mul, map_mul, l5_glFin_archRealGLAt hw m, one_mul]

private theorem l5_exists_compact_support (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : HasCompactSupport α)
    {S : Set Ent} (hS : IsCompact S) (hSd : S ⊆ tcDetSet) :
    ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ e' ∈ S, ∀ y ∉ C, α (archRealLiftAt hw e' * y) = 0 := by
  have hS' : IsCompact (tcInv '' S) := hS.image_of_continuousOn (tc_contDiffOn_tcInv.continuousOn.mono hSd)
  have hS'd : tcInv '' S ⊆ tcDetSet := by
    rintro _ ⟨e', he', rfl⟩
    exact tc_tcInv_mem (hSd he')
  have hcont : ContinuousOn (fun p : Ent × AdelicGL2 (𝓞 K) K => archRealLiftAt hw p.1 * p.2)
      ((tcInv '' S) ×ˢ tsupport α) :=
    ((l5_continuousOn_lift hw).comp continuousOn_fst fun p hp => hS'd hp.1).mul continuousOn_snd
  refine ⟨(fun p : Ent × AdelicGL2 (𝓞 K) K => archRealLiftAt hw p.1 * p.2) '' ((tcInv '' S) ×ˢ tsupport α),
    (hS'.prod (hα : IsCompact (tsupport α))).image_of_continuousOn hcont, ?_⟩
  · intro e' he' y hy
    by_contra hne
    apply hy
    refine ⟨(tcInv e', archRealLiftAt hw e' * y), ⟨⟨e', he', rfl⟩, subset_tsupport _ hne⟩, ?_⟩
    show archRealLiftAt hw (tcInv e') * (archRealLiftAt hw e' * y) = y
    rw [← l5_lift_inv hw (hSd he'), inv_mul_cancel_left]

private theorem l5_integrable_conv_integrand {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

private theorem l5_continuous_rightConv {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hα : IsFactorizableTestFn K α) : Continuous (rightConv K φ α) := by
  obtain ⟨hαc, hαs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ g : AdelicGL2 (𝓞 K) K,
      Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    l5_integrable_conv_integrand hφ hαc hαs
  have hαn : Integrable (fun y => ‖α y‖) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hαc.integrable_of_hasCompactSupport hαs).norm
  obtain ⟨I, hI⟩ : ∃ I : ℝ, (∫ y, ‖α y‖ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) = I := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hI ▸ integral_nonneg fun y => norm_nonneg _
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have key : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ g in 𝓝 g₀, dist (rightConv K φ α g) (rightConv K φ α g₀) ≤ δ * I := by
    intro δ hδ
    obtain ⟨v, hv, hvδ⟩ := (hαs : IsCompact (tsupport α)).mem_uniformity_of_prod (f := fun g y => φ (g * y))
      (s := Set.univ) (q := g₀) (hφ.comp (continuous_fst.mul continuous_snd)).continuousOn (Set.mem_univ g₀)
      (Metric.dist_mem_uniformity hδ)
    rw [nhdsWithin_univ] at hv
    refine Filter.eventually_of_mem hv fun g hg => ?_
    rw [dist_eq_norm, ← hI]
    show ‖(∫ y, φ (g * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) -
        ∫ y, φ (g₀ * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤
      δ * ∫ y, ‖α y‖ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    rw [← integral_sub (hint g) (hint g₀), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hαn.const_mul δ) (Filter.Eventually.of_forall fun y => ?_)
    show ‖φ (g * y) * α y - φ (g₀ * y) * α y‖ ≤ δ * ‖α y‖
    by_cases hy : y ∈ tsupport α
    · have hd : dist (φ (g * y)) (φ (g₀ * y)) < δ := hvδ g hg y hy
      rw [← sub_mul, norm_mul, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
    · have h0 : α y = 0 := by
        by_contra h
        exact hy (subset_tsupport α h)
      simp only [h0, mul_zero, sub_zero, norm_zero, le_refl]
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 : 0 < I + 1 := by linarith
  filter_upwards [key (ε / (I + 1)) (div_pos hε h1)] with g hg
  refine hg.trans_lt ?_
  calc ε / (I + 1) * I < ε / (I + 1) * (I + 1) := mul_lt_mul_of_pos_left (lt_add_one I) (div_pos hε h1)
    _ = ε := by field_simp

end TestData

section EngineBridge

open MeasureTheory Metric Set

section Engine

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private structure TcFamily (F : X → Ent → Y) : Prop where
  smooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (F x) tcDetSet
  meas : ∀ m : ℕ, ∀ e ∈ tcDetSet, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (F x) e) ν
  bound : ∀ e₀ ∈ tcDetSet, ∀ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ball e₀ ρ ⊆ tcDetSet ∧
    ∃ C : ℝ, ∀ᵐ x ∂ν, ∀ e ∈ ball e₀ ρ, ‖iteratedFDeriv ℝ m (F x) e‖ ≤ C

variable {ν}

private theorem tc_aesm_of_zero {g : X → Ent → Y} {e : Ent}
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (g x) e) ν) :
    AEStronglyMeasurable (fun x => g x e) ν := by
  have hfun : (fun x => g x e) =
      fun x => (continuousMultilinearCurryFin0 ℝ Ent Y) (iteratedFDeriv ℝ 0 (g x) e) := by
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryFin0 ℝ Ent Y).continuous.comp_aestronglyMeasurable h

private theorem tc_aesm_fderiv_order {F : X → Ent → Y} (hF : TcFamily ν F) (m : ℕ) {e : Ent} (he : e ∈ tcDetSet) :
    AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) ν := by
  have hfun : (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) =
      fun x => (continuousMultilinearCurryRightEquiv' ℝ m Ent Y) (iteratedFDeriv ℝ (m + 1) (F x) e) := by
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryRightEquiv' ℝ m Ent Y).continuous.comp_aestronglyMeasurable
    (hF.meas (m + 1) e he)

private theorem tc_norm_fderiv_eq (f : Ent → Y) (e : Ent) : ‖fderiv ℝ f e‖ = ‖iteratedFDeriv ℝ 1 f e‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]

private theorem tc_differentiableAt {F : X → Ent → Y} (hF : TcFamily ν F) (x : X) {e : Ent} (he : e ∈ tcDetSet) :
    DifferentiableAt ℝ (F x) e :=
  ((hF.smooth x).differentiableOn (by simp) e he).differentiableAt (tc_isOpen_detSet.mem_nhds he)

private theorem tc_integrable_fderiv [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) :
    Integrable (fun x => fderiv ℝ (F x) e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 1
  refine Integrable.of_bound (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀)) C (hC.mono fun x hx => ?_)
  rw [tc_norm_fderiv_eq]
  exact hx e₀ (mem_ball_self hρ)

private theorem tc_integrable_zero [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) : Integrable (fun x => F x e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 0
  refine Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C (hC.mono fun x hx => ?_)
  have h0 := hx e₀ (mem_ball_self hρ)
  rwa [norm_iteratedFDeriv_zero] at h0

private theorem tc_hasFDerivAt_integral [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) :
    HasFDerivAt (fun e => ∫ x, F x e ∂ν) (∫ x, fderiv ℝ (F x) e₀ ∂ν) e₀ := by
  obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ 1
  obtain ⟨ρ₀, hρ₀, -, C₀, hC₀⟩ := hF.bound e₀ he₀ 0
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun e x => F x e)
    (F' := fun e x => fderiv ℝ (F x) e) (x₀ := e₀) (bound := fun _ => C) (ball_mem_nhds e₀ hρ)
    (Filter.eventually_of_mem (tc_isOpen_detSet.mem_nhds he₀) fun e he => tc_aesm_of_zero (hF.meas 0 e he))
    (Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C₀ (hC₀.mono fun x hx => by
      have h0 := hx e₀ (mem_ball_self hρ₀)
      rwa [norm_iteratedFDeriv_zero] at h0))
    (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀))
    (hC.mono fun x hx e he => by rw [tc_norm_fderiv_eq]; exact hx e he)
    (integrable_const C)
    (Filter.Eventually.of_forall fun x e he => (tc_differentiableAt hF x (hball he)).hasFDerivAt)
  exact h

private theorem tc_contDiffOn_integral_nat [IsFiniteMeasure ν] (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : X → Ent → Z),
      TcFamily ν F → ContDiffOn ℝ n (fun e => ∫ x, F x e ∂ν) tcDetSet := by
  induction n with
  | zero =>
    intro Z _ _ F hF
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun e he => (tc_hasFDerivAt_integral hF he).continuousAt.continuousWithinAt
  | succ n ih =>
    intro Z _ _ F hF
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen tc_isOpen_detSet]
    refine ⟨fun e he => (tc_hasFDerivAt_integral hF he).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hF' : TcFamily ν fun x => fderiv ℝ (F x) :=
      { smooth := fun x => (hF.smooth x).fderiv_of_isOpen tc_isOpen_detSet (by simp)
        meas := fun m e he => tc_aesm_fderiv_order hF m he
        bound := fun e₀ he₀ m => by
          obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ (m + 1)
          exact ⟨ρ, hρ, hball, C, hC.mono fun x hx e he => by rw [norm_iteratedFDeriv_fderiv]; exact hx e he⟩ }
    exact (ih _ hF').congr fun e he => (tc_hasFDerivAt_integral hF he).fderiv

private theorem tc_contDiffOn_integral [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ∫ x, F x e ∂ν) tcDetSet :=
  contDiffOn_infty.mpr fun n => tc_contDiffOn_integral_nat n F hF

private theorem tc_deriv_integral_comp [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) (γ : ℝ → Ent)
    (hγ : DifferentiableAt ℝ γ 0) (h0 : γ 0 ∈ tcDetSet) :
    deriv (fun t : ℝ => ∫ x, F x (γ t) ∂ν) 0 = ∫ x, deriv (fun t : ℝ => F x (γ t)) 0 ∂ν := by
  have hγ' := hγ.hasDerivAt
  have h1 := (tc_hasFDerivAt_integral hF h0).comp_hasDerivAt (0 : ℝ) hγ'
  have h2 : ∀ x, deriv (fun t : ℝ => F x (γ t)) 0 = fderiv ℝ (F x) (γ 0) (deriv γ 0) := fun x =>
    ((tc_differentiableAt hF x h0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ').deriv
  change deriv ((fun e => ∫ x, F x e ∂ν) ∘ γ) 0 = _
  rw [h1.deriv, ContinuousLinearMap.integral_apply (tc_integrable_fderiv hF h0)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (h2 x).symm)

end Engine

section Affine

variable {X : Type} [MeasurableSpace X] {ν : Measure X}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem af_iteratedFDeriv {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (ξ : ℂ) (c : V) (L : Ent →L[ℝ] V)
    (m : ℕ) (e : Ent) :
    iteratedFDeriv ℝ m (fun e' => ξ • Φ (c + L e')) e =
      ξ • (iteratedFDeriv ℝ m Φ (c + L e)).compContinuousLinearMap fun _ : Fin m => L := by
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) fun v : V => Φ (c + v) := hΦ.comp (contDiff_const.add contDiff_id)
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((fun v : V => Φ (c + v)) ∘ ⇑L) := hΦc.comp L.contDiff
  show iteratedFDeriv ℝ m (ξ • ((fun v : V => Φ (c + v)) ∘ ⇑L)) e = _
  rw [iteratedFDeriv_const_smul_apply (hg.of_le (by exact_mod_cast le_top)).contDiffAt,
    L.iteratedFDeriv_comp_right hΦc e (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]

private theorem af_continuous_closedForm {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) (e : Ent) :
    Continuous fun p : V × (Ent →L[ℝ] V) =>
      (iteratedFDeriv ℝ m Φ (p.1 + p.2 e)).compContinuousLinearMap fun _ : Fin m => p.2 := by
  have hL : Continuous fun p : V × (Ent →L[ℝ] V) => p.2 := continuous_snd
  have hinner : Continuous fun p : V × (Ent →L[ℝ] V) => iteratedFDeriv ℝ m Φ (p.1 + p.2 e) :=
    (hΦ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).comp
      (continuous_fst.add (hL.clm_apply continuous_const))
  have houter : Continuous fun p : V × (Ent →L[ℝ] V) =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin m => Ent)
        (fun _ : Fin m => V) ℂ fun _ : Fin m => p.2 :=
    (ContinuousMultilinearMap.coe_continuous (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin m => Ent) (fun _ : Fin m => V) ℂ)).comp (continuous_pi fun _ => hL)
  have h := houter.clm_apply hinner
  simpa only [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply] using h

private theorem af_family [FiniteDimensional ℝ V] {Φ : V → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {χ : X → ℂ}
    (hχ : AEStronglyMeasurable χ ν) {c : X → V} (hc : AEStronglyMeasurable c ν) {L : X → Ent →L[ℝ] V}
    (hL : AEStronglyMeasurable L ν) {Cχ Cc CL : ℝ} (hχb : ∀ᵐ x ∂ν, ‖χ x‖ ≤ Cχ) (hcb : ∀ᵐ x ∂ν, ‖c x‖ ≤ Cc)
    (hLb : ∀ᵐ x ∂ν, ‖L x‖ ≤ CL) :
    TcFamily ν fun x e => χ x • Φ (c x + L x e) where
  smooth x := ((hΦ.comp (contDiff_const.add (L x).contDiff)).const_smul (χ x)).contDiffOn
  meas m e _ := by
    have hfun : (fun x => iteratedFDeriv ℝ m (fun e' => χ x • Φ (c x + L x e')) e) = fun x =>
        χ x • (fun p : V × (Ent →L[ℝ] V) =>
          (iteratedFDeriv ℝ m Φ (p.1 + p.2 e)).compContinuousLinearMap fun _ : Fin m => p.2) (c x, L x) := by
      funext x
      exact af_iteratedFDeriv hΦ (χ x) (c x) (L x) m e
    rw [hfun]
    exact hχ.smul ((af_continuous_closedForm hΦ m e).comp_aestronglyMeasurable (hc.prodMk hL))
  bound e₀ he₀ m := by
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp tc_isOpen_detSet e₀ he₀

    have hρ : ∀ {x : X} {e : Ent}, ‖c x‖ ≤ Cc → ‖L x‖ ≤ CL → e ∈ ball e₀ (min ε 1) →
        c x + L x e ∈ closedBall (0 : V) (|Cc| + |CL| * (‖e₀‖ + 1)) := by
      intro x e hcx hLx he
      rw [mem_ball_iff_norm] at he
      have he1 : ‖e‖ ≤ ‖e₀‖ + 1 := by
        have h1 := norm_sub_norm_le e e₀
        have h2 : ‖e - e₀‖ < 1 := he.trans_le (min_le_right _ _)
        linarith
      rw [mem_closedBall_zero_iff]
      calc ‖c x + L x e‖ ≤ ‖c x‖ + ‖L x e‖ := norm_add_le _ _
        _ ≤ ‖c x‖ + ‖L x‖ * ‖e‖ := add_le_add le_rfl ((L x).le_opNorm e)
        _ ≤ |Cc| + |CL| * (‖e₀‖ + 1) :=
          add_le_add (hcx.trans (le_abs_self _))
            (mul_le_mul (hLx.trans (le_abs_self _)) he1 (norm_nonneg _) (abs_nonneg _))
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) (|Cc| + |CL| * (‖e₀‖ + 1))).exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn
    refine ⟨min ε 1, lt_min hε one_pos, (ball_subset_ball (min_le_left _ _)).trans hεS, |Cχ| * (|M| * |CL| ^ m), ?_⟩
    filter_upwards [hχb, hcb, hLb] with x hχx hcx hLx
    intro e he
    rw [af_iteratedFDeriv hΦ (χ x) (c x) (L x) m e, norm_smul]
    have hΦb : ‖iteratedFDeriv ℝ m Φ (c x + L x e)‖ ≤ |M| := (hM _ (hρ hcx hLx he)).trans (le_abs_self _)
    have hcomp : ‖(iteratedFDeriv ℝ m Φ (c x + L x e)).compContinuousLinearMap fun _ : Fin m => L x‖ ≤
        |M| * |CL| ^ m := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul hΦb (pow_le_pow_left₀ (norm_nonneg _) (hLx.trans (le_abs_self _)) m) (by positivity)
        (abs_nonneg _)
    exact mul_le_mul (hχx.trans (le_abs_self _)) hcomp (norm_nonneg _) (abs_nonneg _)

end Affine

end EngineBridge

section Conv

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def leftDeriv (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

private theorem l5_archFlowAt_inv (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

private def l5Curve (d : ArchDir) (t : ℝ) : Ent :=
  Matrix.of.symm
    (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))

private theorem l5_curve_mem (d : ArchDir) (t : ℝ) : l5Curve d t ∈ tcDetSet := by
  show (Matrix.of (l5Curve d t)).det ≠ 0
  rw [l5Curve, Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix d t).isUnit).ne_zero

private theorem l5_hasDerivAt_curve (d : ArchDir) :
    HasDerivAt (l5Curve d)
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 :=
  hasDerivAt_of_symm_mul_archFlowMatrix _ d

private theorem l5_archFlowAt_eq_lift (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) = archRealLiftAt hw (l5Curve d t) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [l5Curve, ← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]

private def l5M (y : AdelicGL2 (𝓞 K) K) : l5Ent K := archEntries K (glArch (𝓞 K) K y)

private theorem l5_continuous_M : Continuous (l5M : AdelicGL2 (𝓞 K) K → l5Ent K) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => archEntries K (glArch (𝓞 K) K y)
  exact (l5_continuous_archEntries K).comp (continuous_glArch (𝓞 K) K)

private def l5cD (w : InfinitePlace K) (y : AdelicGL2 (𝓞 K) K) : l5Ent K := l5MulR (l5M y) (l5Const w)

private def l5LD (hw : w.IsReal) (y : AdelicGL2 (𝓞 K) K) : Ent →L[ℝ] l5Ent K := (l5MulR (l5M y)).comp (l5LinMat hw)

private theorem l5_continuous_cD (w : InfinitePlace K) : Continuous (l5cD w) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => l5MulR (l5M y) (l5Const w)
  exact (l5_continuous_mulR.comp l5_continuous_M).clm_apply continuous_const

private theorem l5_continuous_LD (hw : w.IsReal) : Continuous (l5LD (K := K) hw) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => (l5MulR (l5M y)).comp (l5LinMat hw)
  exact (l5_continuous_mulR.comp l5_continuous_M).clm_comp continuous_const

private def l5F (φ : AdelicGL2 (𝓞 K) K → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ)
    (Φ : l5Ent K → ℂ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K → Ent → ℂ :=
  fun y e => (φ (g * y) * ff (glFin (𝓞 K) K y)) • Φ (l5cD w y + l5LD hw y e)

private theorem l5F_eq {φ α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : l5Ent K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) {e : Ent} (he : e ∈ tcDetSet) (y : AdelicGL2 (𝓞 K) K) :
    l5F φ ff Φ hw g y e = φ (g * y) * α (archRealLiftAt hw e * y) := by
  rw [l5_factor_lift_mul hw hfa hα he y]
  simp only [l5F, l5cD, l5LD, l5M, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

private theorem l5_tcFamily {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsLocallyConstant ff) {Φ : l5Ent K → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) {C : Set (AdelicGL2 (𝓞 K) K)}
    (hC : IsCompact C) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    TcFamily ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) (l5F φ ff Φ hw g) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hχ : Continuous fun y : AdelicGL2 (𝓞 K) K => φ (g * y) * ff (glFin (𝓞 K) K y) :=
    (hφ.comp (continuous_const.mul continuous_id)).mul (hff.continuous.comp (continuous_glFin (𝓞 K) K))
  obtain ⟨Cχ, hCχ⟩ := hC.exists_bound_of_continuousOn hχ.continuousOn
  obtain ⟨Cc, hCc⟩ := hC.exists_bound_of_continuousOn (l5_continuous_cD w).continuousOn
  obtain ⟨CL, hCL⟩ := hC.exists_bound_of_continuousOn (l5_continuous_LD hw).continuousOn
  exact af_family hΦ hχ.aestronglyMeasurable (l5_continuous_cD w).aestronglyMeasurable
    (l5_continuous_LD hw).aestronglyMeasurable (ae_restrict_of_forall_mem hCm hCχ) (ae_restrict_of_forall_mem hCm hCc)
    (ae_restrict_of_forall_mem hCm hCL)

private theorem l5_rightConv_lift_eq {φ α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : l5Ent K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) {C : Set (AdelicGL2 (𝓞 K) K)} {S : Set Ent} (hSd : S ⊆ tcDetSet)
    (hCvan : ∀ e' ∈ S, ∀ y ∉ C, α (archRealLiftAt hw e' * y) = 0) {e' : Ent} (he' : e' ∈ S) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    rightConv K φ (fun y => α (archRealLiftAt hw e' * y)) g =
      ∫ y, l5F φ ff Φ hw g y e' ∂((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  have hz : ∀ y, y ∉ C → φ (g * y) * α (archRealLiftAt hw e' * y) = 0 := fun y hy => by
    rw [hCvan e' he' y hy, mul_zero]
  show (∫ y, φ (g * y) * α (archRealLiftAt hw e' * y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => (l5F_eq hfa hα hw g (hSd he') y).symm)

private theorem l5_rightConv_add_right {φ α₁ α₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hα₁c : Continuous α₁)
    (hα₁s : HasCompactSupport α₁) (hα₂c : Continuous α₂) (hα₂s : HasCompactSupport α₂) :
    rightConv K φ (α₁ + α₂) = rightConv K φ α₁ + rightConv K φ α₂ := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (α₁ + α₂) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    (∫ y, φ (g * y) * α₁ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) +
      ∫ y, φ (g * y) * α₂ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_add (l5_integrable_conv_integrand hφ hα₁c hα₁s g) (l5_integrable_conv_integrand hφ hα₂c hα₂s g)]
  congr 1
  funext y
  rw [Pi.add_apply, mul_add]

private theorem l5_rightConv_smul_right (φ α : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K φ (c • α) = c • rightConv K φ α := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (c • α) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    c * ∫ y, φ (g * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  ring

private theorem l5_isArchSmoothAt_rightConv (hw : w.IsReal) {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hα : IsFactorizableTestFn K α) : IsArchSmoothAt hw (rightConv K φ α) := by
  obtain ⟨-, hαs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, ⟨hff, -⟩, hαeq⟩ := hα
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  intro g
  refine contDiffOn_of_locally_contDiffOn fun e₀ he₀ => ?_
  have he₀' : tcInv e₀ ∈ tcDetSet := tc_tcInv_mem he₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 tc_isOpen_detSet (tcInv e₀) he₀'
  have hSd : closedBall (tcInv e₀) (ρ / 2) ⊆ tcDetSet :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hball
  obtain ⟨C, hC, hCvan⟩ := l5_exists_compact_support hw hαs (isCompact_closedBall (tcInv e₀) (ρ / 2)) hSd
  haveI : IsFiniteMeasure ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hH := tc_contDiffOn_integral (l5_tcFamily hφ hff hΦ hw g hC)
  refine ⟨tcDetSet ∩ tcInv ⁻¹' ball (tcInv e₀) (ρ / 2),
    tc_contDiffOn_tcInv.continuousOn.isOpen_inter_preimage tc_isOpen_detSet isOpen_ball,
    ⟨he₀, mem_ball_self (half_pos hρ)⟩, ?_⟩
  refine (hH.comp (tc_contDiffOn_tcInv.mono fun e he => he.1) fun e he => tc_tcInv_mem he.1).congr fun e he => ?_
  have hinS : tcInv e ∈ closedBall (tcInv e₀) (ρ / 2) := ball_subset_closedBall he.2.2
  show rightConv K φ α (g * archRealLiftAt hw e) = _
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, l5_lift_inv hw he.1]
  exact l5_rightConv_lift_eq hfa hαeq hw g hSd hCvan hinS

private theorem l5_archDerivAt_rightConv (hw : w.IsReal) (d : ArchDir) {φ α : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hα : IsFactorizableTestFn K α) :
    archDerivAt hw d (rightConv K φ α) = rightConv K φ (leftDeriv hw d α) := by
  obtain ⟨-, hαs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, ⟨hff, -⟩, hαeq⟩ := hα
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  funext g

  have hγ : HasDerivAt (fun t : ℝ => l5Curve d (-t))
      ((-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 := by
    have h := l5_hasDerivAt_curve d
    rw [← neg_zero] at h
    exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h0 : l5Curve d (-0) ∈ tcDetSet := l5_curve_mem d _
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 tc_isOpen_detSet (l5Curve d (-0)) h0
  have hSd : closedBall (l5Curve d (-0)) (ρ / 2) ⊆ tcDetSet := (closedBall_subset_ball (half_lt_self hρ)).trans hball
  obtain ⟨C, hC, hCvan⟩ := l5_exists_compact_support hw hαs (isCompact_closedBall (l5Curve d (-0)) (ρ / 2)) hSd
  haveI : IsFiniteMeasure ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hF := l5_tcFamily hφ hff hΦ hw g hC

  have hev : ∀ᶠ t : ℝ in 𝓝 0, l5Curve d (-t) ∈ closedBall (l5Curve d (-0)) (ρ / 2) :=
    hγ.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (half_pos hρ))

  have hL : archDerivAt hw d (rightConv K φ α) g =
      deriv (fun t : ℝ => ∫ y, l5F φ ff Φ hw g y (l5Curve d (-t))
        ∂((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).restrict C)) 0 := by
    show deriv (fun t : ℝ => rightConv K φ α (g * archFlowAt hw d t)) 0 = _
    refine Filter.EventuallyEq.deriv_eq (hev.mono fun t ht => ?_)
    show rightConv K φ α (g * archFlowAt hw d t) = _
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, l5_archFlowAt_inv, l5_archFlowAt_eq_lift]
    exact l5_rightConv_lift_eq hfa hαeq hw g hSd hCvan ht

  have hpt : ∀ y : AdelicGL2 (𝓞 K) K, deriv (fun t : ℝ => l5F φ ff Φ hw g y (l5Curve d (-t))) 0 =
      φ (g * y) * leftDeriv hw d α y := by
    intro y
    have hfun : (fun t : ℝ => l5F φ ff Φ hw g y (l5Curve d (-t))) =
        fun t : ℝ => φ (g * y) * α (archFlowAt hw d (-t) * y) := by
      funext t
      rw [l5F_eq hfa hαeq hw g (l5_curve_mem d (-t)) y, l5_archFlowAt_eq_lift]
    rw [hfun]
    show deriv (fun t : ℝ => φ (g * y) * α (archFlowAt hw d (-t) * y)) 0 =
      φ (g * y) * deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0
    exact deriv_const_mul_field _

  have hvan : ∀ y ∉ C, leftDeriv hw d α y = 0 := by
    intro y hy
    have h : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      refine hev.mono fun t ht => ?_
      show α (archFlowAt hw d (-t) * y) = 0
      rw [l5_archFlowAt_eq_lift]
      exact hCvan _ ht y hy
    show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 = 0
    rw [h.deriv_eq, deriv_const]
  rw [hL, tc_deriv_integral_comp hF (fun t => l5Curve d (-t)) hγ.differentiableAt h0]
  have hz : ∀ y, y ∉ C → φ (g * y) * leftDeriv hw d α y = 0 := fun y hy => by rw [hvan y hy, mul_zero]
  show _ = ∫ y, φ (g * y) * leftDeriv hw d α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

private theorem l5_leftDeriv_inv (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) :
    leftDeriv hw d α y⁻¹ = archDerivAt hw d (fun z => α z⁻¹) y := by
  show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y⁻¹)) 0 = deriv (fun t : ℝ => α (y * archFlowAt hw d t)⁻¹) 0
  congr 1
  funext t
  rw [mul_inv_rev, l5_archFlowAt_inv]

private theorem l5_isArchSmoothAt_comp_inv (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw fun z => α z⁻¹ := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, -, hαeq⟩ := hα
  intro g
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun e : Ent => Φ (l5cD w g⁻¹ + l5LD hw g⁻¹ (tcInv e)) * ff (glFin (𝓞 K) K g⁻¹)) tcDetSet :=
    (hΦ.comp_contDiffOn (contDiffOn_const.add ((l5LD hw g⁻¹).contDiff.comp_contDiffOn tc_contDiffOn_tcInv))).mul
      contDiffOn_const
  refine hsm.congr fun e he => ?_
  show α (g * archRealLiftAt hw e)⁻¹ = _
  rw [mul_inv_rev, l5_lift_inv hw he, l5_factor_lift_mul hw hfa hαeq (tc_det_tcInv he)]
  rfl

end Conv

section LeftDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def l5Dir (d : ArchDir) : Ent :=
  (-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)

private theorem l5_hasDerivAt_curve_neg (d : ArchDir) : HasDerivAt (fun t : ℝ => l5Curve d (-t)) (l5Dir d) 0 := by
  have h := l5_hasDerivAt_curve d
  rw [← neg_zero] at h
  exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

private theorem l5_curve_det (d : ArchDir) (t : ℝ) : (Matrix.of (l5Curve d t)).det ≠ 0 := l5_curve_mem d t

private theorem l5MulR_eq_mulL (N X : l5Ent K) : l5MulR N X = l5MulL X N := rfl

private def l5Phi' (hw : w.IsReal) (d : ArchDir) (Φ : l5Ent K → ℂ) (N : l5Ent K) : ℂ :=
  fderiv ℝ Φ (l5MulL (l5Const w) N + l5MulL (l5LinMat hw (l5Curve d (-0))) N) (l5MulL (l5LinMat hw (l5Dir d)) N)

private theorem l5_contDiff_Phi' (hw : w.IsReal) (d : ArchDir) {Φ : l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (l5Phi' hw d Φ) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2.comp
    ((l5MulL (l5Const w)).contDiff.add (l5MulL (l5LinMat hw (l5Curve d (-0)))).contDiff)).clm_apply
    (l5MulL (l5LinMat hw (l5Dir d))).contDiff

private theorem l5_hasDerivAt_Phi_curve (hw : w.IsReal) (d : ArchDir) {Φ : l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (N : l5Ent K) :
    HasDerivAt (fun t : ℝ => Φ (l5MulR N (l5Const w) + l5MulR N (l5LinMat hw (l5Curve d (-t)))))
      (l5Phi' hw d Φ N) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => l5LinMat hw (l5Curve d (-t))) (l5LinMat hw (l5Dir d)) 0 :=
    (l5LinMat hw).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (l5_hasDerivAt_curve_neg d)
  have h2 : HasDerivAt (fun t : ℝ => l5MulR N (l5LinMat hw (l5Curve d (-t)))) (l5MulR N (l5LinMat hw (l5Dir d))) 0 :=
    (l5MulR N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => l5MulR N (l5Const w) + l5MulR N (l5LinMat hw (l5Curve d (-t))))
      (l5MulR N (l5LinMat hw (l5Dir d))) 0 :=
    h2.const_add (l5MulR N (l5Const w))
  have h4 := ((contDiff_infty_iff_fderiv.1 hΦ).1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [l5Phi', ← l5MulR_eq_mulL]
  exact h4

private theorem l5_fa_lift_mul (hw : w.IsReal) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {Φ : l5Ent K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) {e : Ent} (he : (Matrix.of e).det ≠ 0)
    (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    fa (glArch (𝓞 K) K (archRealLiftAt hw e) * z) =
      Φ (l5MulR (archEntries K z) (l5Const w) + l5MulR (archEntries K z) (l5LinMat hw e)) := by
  rw [hfa, ← map_add, l5MulR_apply, ← l5_archEntries_glArch_lift hw he, ← l5_archEntries_mul, Equiv.symm_apply_apply]

private theorem l5_glFin_archFlowAt (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    glFin (𝓞 K) K (archFlowAt hw d t) = 1 := by
  rw [l5_archFlowAt_eq_lift]
  exact l5_glFin_lift hw (l5_curve_det d t)

private theorem l5_leftDeriv_eq (hw : w.IsReal) (d : ArchDir) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (y : AdelicGL2 (𝓞 K) K) :
    leftDeriv hw d α y = l5Phi' hw d Φ (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) = fun t : ℝ =>
      Φ (l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5Const w) +
          l5MulR (archEntries K (glArch (𝓞 K) K y)) (l5LinMat hw (l5Curve d (-t)))) *
        ff (glFin (𝓞 K) K y) := by
    funext t
    rw [l5_archFlowAt_eq_lift, l5_factor_lift_mul hw hfa hα (l5_curve_det d (-t)) y]
  show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact ((l5_hasDerivAt_Phi_curve hw d hΦ _).mul_const _).deriv

private theorem l5_hasCompactSupport_Phi' (hw : w.IsReal) (d : ArchDir) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {Φ : l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) : HasCompactSupport fun z => l5Phi' hw d Φ (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  simp only [Function.mem_support] at hz
  by_contra hzt
  apply hz

  have hcurve : ContinuousAt (fun t : ℝ => l5Curve d (-t)) 0 := (l5_hasDerivAt_curve_neg d).continuousAt
  have hlift : ContinuousAt (fun t : ℝ => (archRealLiftAt hw (l5Curve d (-t)) : AdelicGL2 (𝓞 K) K)) 0 :=
    ContinuousAt.comp_of_eq
      ((l5_continuousOn_lift hw).continuousAt (tc_isOpen_detSet.mem_nhds (l5_curve_mem d (-0)))) hcurve rfl
  have horbit : ContinuousAt (fun t : ℝ => glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-t))) * z) 0 :=
    ((continuous_glArch (𝓞 K) K).continuousAt.comp hlift).mul continuousAt_const
  have hz0 : glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-0)) : AdelicGL2 (𝓞 K) K) * z = z := by
    rw [← l5_archFlowAt_eq_lift, neg_zero, archFlowAt_zero, map_one, one_mul]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, fa (glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-t))) * z) = 0 := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-0)) : AdelicGL2 (𝓞 K) K) * z) := by
      rw [hz0]
      exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hzt
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hfun : (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-t))) * z)) = fun t : ℝ =>
      Φ (l5MulR (archEntries K z) (l5Const w) + l5MulR (archEntries K z) (l5LinMat hw (l5Curve d (-t)))) := by
    funext t
    exact l5_fa_lift_mul hw hfa (l5_curve_det d (-t)) z
  have hd : HasDerivAt (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-t))) * z))
      (l5Phi' hw d Φ (archEntries K z)) 0 := by
    rw [hfun]
    exact l5_hasDerivAt_Phi_curve hw d hΦ (archEntries K z)
  have heq : (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (l5Curve d (-t))) * z)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => (0 : ℂ) :=
    hev.mono fun t ht => ht
  rw [← hd.deriv, heq.deriv_eq, deriv_const]

private theorem l5_isFactorizableTestFn_leftDeriv (hw : w.IsReal) (d : ArchDir) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) : IsFactorizableTestFn K (leftDeriv hw d α) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩ := hα
  exact ⟨fun z => l5Phi' hw d Φ (archEntries K z), ff,
    ⟨⟨l5Phi' hw d Φ, l5_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, l5_hasCompactSupport_Phi' hw d hΦ hfa hsupp⟩, hff,
    l5_leftDeriv_eq hw d hΦ hfa hαeq⟩

private theorem l5_leftDeriv_tensor (hw : w.IsReal) (d : ArchDir) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
      leftDeriv hw d (fun z => fa (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z)) =
        fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨fun z => l5Phi' hw d Φ (archEntries K z),
    ⟨⟨l5Phi' hw d Φ, l5_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, l5_hasCompactSupport_Phi' hw d hΦ hfaΦ hsupp⟩, ?_⟩
  funext y
  exact l5_leftDeriv_eq hw d hΦ hfaΦ (fun _ => rfl) y

end LeftDerivFactor

section Parts

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem l5_continuous_archFlowAt (hw : w.IsReal) (d : ArchDir) :
    Continuous fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) := by
  have h0 : ContinuousAt (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) 0 := by
    have hfun : (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) =
        fun t : ℝ => archRealLiftAt hw (l5Curve d t) := by
      funext t
      exact l5_archFlowAt_eq_lift hw d t
    rw [hfun]
    exact ((l5_continuousOn_lift hw).continuousAt (tc_isOpen_detSet.mem_nhds (l5_curve_mem d 0))).comp
      (l5_hasDerivAt_curve d).continuousAt
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hfun : (fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)) =
      fun t : ℝ => archFlowAt hw d t₀ * archFlowAt hw d (t - t₀) := by
    funext t
    rw [← archFlowAt_add, show t₀ + (t - t₀) = t by ring]
  rw [hfun]
  have hsub : ContinuousAt (fun t : ℝ => t - t₀) t₀ := continuousAt_id.sub continuousAt_const
  have hshift : ContinuousAt (fun t : ℝ => (archFlowAt hw d (t - t₀) : AdelicGL2 (𝓞 K) K)) t₀ :=
    ContinuousAt.comp_of_eq (g := fun s : ℝ => (archFlowAt hw d s : AdelicGL2 (𝓞 K) K)) (f := fun t : ℝ => t - t₀)
      h0 hsub (sub_self t₀)
  exact continuousAt_const.mul hshift

private theorem l5_hasDerivAt_orbit (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsArchSmoothAt hw f) (x : AdelicGL2 (𝓞 K) K) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => f (x * archFlowAt hw d t)) (archDerivAt hw d f (x * archFlowAt hw d t₀)) t₀ := by
  have h0 : ∀ x' : AdelicGL2 (𝓞 K) K,
      HasDerivAt (fun s : ℝ => f (x' * archFlowAt hw d s)) (archDerivAt hw d f x') 0 := by
    intro x'
    have hfun : (fun s : ℝ => f (x' * archFlowAt hw d s)) = fun s : ℝ => f (x' * archRealLiftAt hw (l5Curve d s)) := by
      funext s
      rw [l5_archFlowAt_eq_lift]
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => f (x' * archFlowAt hw d s)) 0 := by
      rw [hfun]
      exact (((hf x').differentiableOn (by simp) _ (l5_curve_mem d 0)).differentiableAt
        (tc_isOpen_detSet.mem_nhds (l5_curve_mem d 0))).comp (0 : ℝ) (l5_hasDerivAt_curve d).differentiableAt
    exact hdiff.hasDerivAt
  have hfun : (fun t : ℝ => f (x * archFlowAt hw d t)) =
      (fun s : ℝ => f (x * archFlowAt hw d t₀ * archFlowAt hw d s)) ∘ fun t : ℝ => t - t₀ := by
    funext t
    show f (x * archFlowAt hw d t) = f (x * archFlowAt hw d t₀ * archFlowAt hw d (t - t₀))
    rw [mul_assoc, ← archFlowAt_add, show t₀ + (t - t₀) = t by ring]
  have hpt : HasDerivAt (fun s : ℝ => f (x * archFlowAt hw d t₀ * archFlowAt hw d s))
      (archDerivAt hw d f (x * archFlowAt hw d t₀)) (t₀ - t₀) := by
    rw [sub_self]
    exact h0 _
  rw [hfun]
  have h := hpt.scomp (h := fun t : ℝ => t - t₀) t₀ ((hasDerivAt_sub_const_iff t₀).2 (hasDerivAt_id t₀))
  rw [one_smul] at h
  exact h

private theorem l5_archDerivAt_eq_zero_of_notMem (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    {y : AdelicGL2 (𝓞 K) K} (hy : y ∉ tsupport f) : archDerivAt hw d f y = 0 := by
  have hmem : (tsupport f)ᶜ ∈ 𝓝 (y * archFlowAt hw d 0) := by
    rw [archFlowAt_zero, mul_one]
    exact (isClosed_tsupport f).isOpen_compl.mem_nhds hy
  have horbit : ContinuousAt (fun t : ℝ => y * archFlowAt hw d t) 0 :=
    continuousAt_const.mul (l5_continuous_archFlowAt hw d).continuousAt
  have heq : (fun t : ℝ => f (y * archFlowAt hw d t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv (fun t : ℝ => f (y * archFlowAt hw d t)) 0 = 0
  rw [heq.deriv_eq, deriv_const]

private theorem l5_hasCompactSupport_archDerivAt (hw : w.IsReal) (d : ArchDir) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (archDerivAt hw d f) := by
  refine hf.mono' fun y hy => ?_
  by_contra hyt
  exact hy (l5_archDerivAt_eq_zero_of_notMem hw d hyt)

private theorem l5_hasCompactSupport_mul {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : HasCompactSupport f)
    (h : AdelicGL2 (𝓞 K) K → ℂ) : HasCompactSupport fun y => f y * h y := by
  refine hf.mono fun y hy => ?_
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by rw [h0, zero_mul])

private def l5E (hw : w.IsReal) (d : ArchDir) (φ γ ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  φ (g * y * archFlowAt hw d t) * (γ (y * archFlowAt hw d t) * ω y)

private def l5E' (hw : w.IsReal) (d : ArchDir) (φ γ ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  archDerivAt hw d φ (g * y * archFlowAt hw d t) * (γ (y * archFlowAt hw d t) * ω y) +
    φ (g * y * archFlowAt hw d t) * (archDerivAt hw d γ (y * archFlowAt hw d t) * ω y)

private theorem l5_hasDerivAt_E (hw : w.IsReal) (d : ArchDir) {φ γ : AdelicGL2 (𝓞 K) K → ℂ} (hφs : IsArchSmoothAt hw φ)
    (hγs : IsArchSmoothAt hw γ) (ω : AdelicGL2 (𝓞 K) K → ℂ) (g y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => l5E hw d φ γ ω g t' y) (l5E' hw d φ γ ω g t y) t :=
  (l5_hasDerivAt_orbit hw d hφs (g * y) t).mul ((l5_hasDerivAt_orbit hw d hγs y t).mul_const (ω y))

private theorem l5_continuous_E' (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ) (hγ' : Continuous (archDerivAt hw d γ))
    (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) :
    Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => l5E' hw d φ γ ω g p.1 p.2 := by
  have hflow : Continuous fun t : ℝ => (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) := l5_continuous_archFlowAt hw d
  unfold l5E'
  fun_prop

private theorem l5_E'_eq_zero (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 K) K → ℂ) {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (ω : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) {t : ℝ} {y : AdelicGL2 (𝓞 K) K}
    (hy : y * archFlowAt hw d t ∉ tsupport γ) : l5E' hw d φ γ ω g t y = 0 := by
  rw [l5E', image_eq_zero_of_notMem_tsupport hy, l5_archDerivAt_eq_zero_of_notMem hw d hy]
  ring

private theorem l5_integral_E_eq (hw : w.IsReal) (d : ArchDir) (φ γ : AdelicGL2 (𝓞 K) K → ℂ)
    {ω : AdelicGL2 (𝓞 K) K → ℂ} (hωinv : ∀ y t, ω (y * archFlowAt hw d t) = ω y) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    (∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∫ y, φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isMulRightInvariant_adelicGLHaar K
  rw [← integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun y => φ (g * y) * (γ y * ω y)) (archFlowAt hw d t)]
  congr 1
  funext y
  rw [l5E, hωinv, mul_assoc]

private theorem l5_continuous_E (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hγ : Continuous γ) (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    Continuous fun y => l5E hw d φ γ ω g t y := by
  unfold l5E
  exact (hφ.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul
    ((hγ.comp (continuous_id.mul continuous_const)).mul hω)

private theorem l5_exists_segment_compact (hw : w.IsReal) (d : ArchDir) {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγc : HasCompactSupport γ) : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧
      ∀ y, y ∉ C → ∀ t ∈ ball (0 : ℝ) 1, y * archFlowAt hw d t ∉ tsupport γ := by
  refine ⟨(fun p : ℝ × AdelicGL2 (𝓞 K) K => p.2 * archFlowAt hw d (-p.1)) '' (closedBall (0 : ℝ) 1 ×ˢ tsupport γ),
    ((isCompact_closedBall (0 : ℝ) 1).prod (hγc : IsCompact (tsupport γ))).image
      (continuous_snd.mul ((l5_continuous_archFlowAt hw d).comp continuous_fst.neg)), ?_⟩
  intro y hy t ht hmem
  apply hy
  refine ⟨(t, y * archFlowAt hw d t), ⟨ball_subset_closedBall ht, hmem⟩, ?_⟩
  show y * archFlowAt hw d t * archFlowAt hw d (-t) = y
  rw [mul_assoc, ← archFlowAt_add, add_neg_cancel, archFlowAt_zero, mul_one]

private theorem l5_hasDerivAt_integral_E (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAt hw γ) (hγ' : Continuous (archDerivAt hw d γ))
    (hω : Continuous ω) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      (∫ y, l5E' hw d φ γ ω g 0 y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) 0 := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨C, hC, hCout⟩ := l5_exists_segment_compact hw d (γ := γ) hγc
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hC).exists_bound_of_continuousOn
    (l5_continuous_E' hw d hφ hφ' hγ hγ' hω g).continuousOn
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hbound : Integrable (fun y => if y ∈ C then M else 0) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hCm
  have hint0 : Integrable (fun y => l5E hw d φ γ ω g 0 y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    have hE0 : (fun y => l5E hw d φ γ ω g 0 y) = fun y => φ (g * y) * (γ y * ω y) := by
      funext y
      rw [l5E, archFlowAt_zero, mul_one, mul_one]
    rw [hE0]
    exact l5_integrable_conv_integrand hφ (hγ.mul hω) (l5_hasCompactSupport_mul hγc ω) g
  have hE'0m : AEStronglyMeasurable (fun y => l5E' hw d φ γ ω g 0 y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    ((l5_continuous_E' hw d hφ hφ' hγ hγ' hω g).comp
      ((continuous_const : Continuous fun _ : AdelicGL2 (𝓞 K) K => (0 : ℝ)).prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K), ∀ t ∈ ball (0 : ℝ) 1,
      ‖l5E' hw d φ γ ω g t y‖ ≤ if y ∈ C then M else 0 := by
    refine Filter.Eventually.of_forall fun y t ht => ?_
    by_cases hy : y ∈ C
    · rw [if_pos hy]
      exact hM (t, y) ⟨ball_subset_closedBall ht, hy⟩
    · rw [if_neg hy, l5_E'_eq_zero hw d φ ω g (hCout y hy t ht), norm_zero]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (F := l5E hw d φ γ ω g) (F' := l5E' hw d φ γ ω g) (ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t => (l5_continuous_E hw d hφ hγ hω g t).aestronglyMeasurable) hint0 hE'0m
    h_bound hbound (Filter.Eventually.of_forall fun y t _ => l5_hasDerivAt_E hw d hφs hγs ω g y t)).2

private theorem l5_rightConv_archDerivAt_mul (hw : w.IsReal) (d : ArchDir) {φ γ ω : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAt hw γ) (hγ' : Continuous (archDerivAt hw d γ))
    (hω : Continuous ω) (hωinv : ∀ y t, ω (y * archFlowAt hw d t) = ω y) :
    rightConv K φ (fun y => archDerivAt hw d γ y * ω y) =
      -rightConv K (archDerivAt hw d φ) fun y => γ y * ω y := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  funext g

  have hA : Integrable (fun y => archDerivAt hw d φ (g * y) * (γ y * ω y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    l5_integrable_conv_integrand hφ' (hγ.mul hω) (l5_hasCompactSupport_mul hγc ω) g
  have hB : Integrable (fun y => φ (g * y) * (archDerivAt hw d γ y * ω y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    l5_integrable_conv_integrand hφ (hγ'.mul hω)
      (l5_hasCompactSupport_mul (l5_hasCompactSupport_archDerivAt hw d hγc) ω) g
  have hD : HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      (∫ y, l5E' hw d φ γ ω g 0 y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) 0 :=
    l5_hasDerivAt_integral_E hw d hφ hφs hφ' hγ hγc hγs hγ' hω g

  have hconst : HasDerivAt (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      0 0 := by
    have hfun : (fun t : ℝ => ∫ y, l5E hw d φ γ ω g t y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
        fun _ => ∫ y, φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
      funext t
      exact l5_integral_E_eq hw d φ γ hωinv g t
    rw [hfun]
    exact hasDerivAt_const (0 : ℝ) _
  have hzero := hD.unique hconst
  have hE'0 : (fun y => l5E' hw d φ γ ω g 0 y) =
      fun y => archDerivAt hw d φ (g * y) * (γ y * ω y) + φ (g * y) * (archDerivAt hw d γ y * ω y) := by
    funext y
    rw [l5E', archFlowAt_zero, mul_one, mul_one]
  rw [hE'0, integral_add hA hB] at hzero
  show (∫ y, φ (g * y) * (archDerivAt hw d γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    -∫ y, archDerivAt hw d φ (g * y) * (γ y * ω y) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  linear_combination hzero

end Parts

section Head

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) :
    (∀ φ α : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsFactorizableTestFn K α →
      IsArchSmoothAt hw (rightConv K φ α) ∧
        archDerivAt hw d (rightConv K φ α) =
          rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)) ∧
    (∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa →
        ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
          (fun y : AdelicGL2 (𝓞 K) K =>
              deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
                ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y))) 0) =
            fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
    (∀ φ γ ω : AdelicGL2 (𝓞 K) K → ℂ,
      Continuous φ → IsArchSmoothAt hw φ → Continuous (archDerivAt hw d φ) →
      Continuous γ → HasCompactSupport γ → IsArchSmoothAt hw γ → Continuous (archDerivAt hw d γ) →
      Continuous ω → (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), ω (y * archFlowAt hw d t) = ω y) →
        rightConv K φ (fun y => archDerivAt hw d γ y * ω y) =
          -rightConv K (archDerivAt hw d φ) fun y => γ y * ω y) := by
  refine ⟨fun φ α hφ hα => ⟨l5_isArchSmoothAt_rightConv hw hφ hα, l5_archDerivAt_rightConv hw d hφ hα⟩,
    fun fa ff hfa => l5_leftDeriv_tensor hw d hfa ff, ?_⟩
  intro φ γ ω hφ hφs hφ' hγ hγc hγs hγ' hω hωinv
  exact l5_rightConv_archDerivAt_mul hw d hφ hφs hφ' hγ hγc hγs hγ' hω hωinv

end Head

end

end S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn (solution)
