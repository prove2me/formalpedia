-- Prove2me | solution 1 for AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/aee9e0ce-4410-50f3-87e2-59d068828d22

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_AutomorphicForm_RightConvolution
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
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
set_option autoImplicit false

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivComplexOfIsComplex isometryEquivComplexOfIsComplex)
open scoped Topology

noncomputable section

private abbrev E8Ent : Type := Fin 2 → Fin 2 → ℂ

private abbrev e8DetSet : Set E8Ent := {e : E8Ent | (Matrix.of e).det ≠ 0}

private theorem e8tc_isOpen_detSet : IsOpen e8DetSet := by
  have h : Continuous fun e : E8Ent => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

section LiftAnalysis

private def e8Inv (e : E8Ent) : E8Ent := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

private theorem e8tc_of_tcInv {e : E8Ent} : Matrix.of (e8Inv e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [e8Inv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

private theorem e8tc_det_tcInv {e : E8Ent} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (e8Inv e)).det ≠ 0 := by
  rw [e8tc_of_tcInv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem e8tc_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : E8Ent => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i).contDiff

private theorem e8tc_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : E8Ent => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((e8tc_contDiff_entry 0 0).mul (e8tc_contDiff_entry 1 1)).sub ((e8tc_contDiff_entry 0 1).mul (e8tc_contDiff_entry 1 0))

private theorem e8tc_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : E8Ent => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact e8tc_contDiff_entry _ _ | exact (e8tc_contDiff_entry _ _).neg

private theorem e8tc_contDiffOn_tcInv : ContDiffOn ℝ (⊤ : ℕ∞) e8Inv e8DetSet :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    ((e8tc_contDiff_adj i j).contDiffOn.mul (e8tc_contDiff_det.contDiffOn.inv fun _ he => he)).congr
      fun e _ => div_eq_mul_inv _ _

private theorem e8tc_tcInv_mem {e : E8Ent} (he : e ∈ e8DetSet) : e8Inv e ∈ e8DetSet := e8tc_det_tcInv he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem e8l5_lift_inv (hw : w.IsComplex) {e : E8Ent} (he : (Matrix.of e).det ≠ 0) :
    (archComplexLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archComplexLiftAt hw (e8Inv e) := by
  rw [archComplexLiftAt_of_det_ne_zero hw he, archComplexLiftAt_of_det_ne_zero hw (e8tc_det_tcInv he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact e8tc_of_tcInv.symm

private def e8l5Theta (hw : w.IsComplex) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (archMatrixUpdate K w (A.map (ringEquivComplexOfIsComplex hw).symm) i j,
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j)

private theorem e8l5_coe_archComplexGLAt (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    ((archComplexGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      e8l5Theta hw (m : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

private theorem e8l5_continuous_Theta (hw : w.IsComplex) : Continuous (e8l5Theta (K := K) hw) := by
  have hentry : ∀ i j : Fin 2, Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j := fun i j =>
    (continuous_apply j).comp (continuous_apply i : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A i)
  have hsymm : Continuous fun r : ℂ => (ringEquivComplexOfIsComplex hw).symm r :=
    (isometryEquivComplexOfIsComplex hw).symm.continuous
  refine continuous_matrix fun i j => Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [archMatrixUpdate_apply_self, Matrix.map_apply]
    exact hsymm.comp (hentry i j)
  · simp only [archMatrixUpdate_apply_of_ne K w _ i j hv]
    exact continuous_const

private theorem e8l5_continuousOn_lift (hw : w.IsComplex) :
    ContinuousOn (fun e : E8Ent => (archComplexLiftAt hw e : AdelicGL2 (𝓞 K) K)) e8DetSet := by
  rw [continuousOn_iff_continuous_restrict]
  have hdet : ∀ e : e8DetSet, (Matrix.of (e : E8Ent)).det ≠ 0 := fun e => e.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : e8DetSet,
        ((archComplexLiftAt hw (e : E8Ent) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          e8l5Theta hw (Matrix.of (e : E8Ent)) := fun e => by
      rw [archComplexLiftAt_of_det_ne_zero hw (hdet e), e8l5_coe_archComplexGLAt]
      rfl
    exact ((e8l5_continuous_Theta hw).comp continuous_subtype_val).congr fun e => (h e).symm
  · have h : ∀ e : e8DetSet,
        (((archComplexLiftAt hw (e : E8Ent) : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = e8l5Theta hw (Matrix.of (e8Inv (e : E8Ent))) := fun e => by
      rw [e8l5_lift_inv hw (hdet e), archComplexLiftAt_of_det_ne_zero hw (e8tc_det_tcInv (hdet e)), e8l5_coe_archComplexGLAt]
      rfl
    exact ((e8l5_continuous_Theta hw).comp
      (continuousOn_iff_continuous_restrict.1 e8tc_contDiffOn_tcInv.continuousOn)).congr fun e => (h e).symm

end LiftAnalysis

section AffineData

open scoped Classical

section FieldOnly

variable (K : Type) [Field K]

private abbrev e8l5Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private theorem e8l5_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem e8l5_continuous_archEntries : Continuous (archEntries K) := by
  have hval : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      (a.val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => (e8l5_continuous_ringEquiv K).comp ?_
  exact (continuous_apply j).comp
    ((continuous_apply i : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m i).comp hval)

private theorem e8l5_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

private theorem e8l5_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  e8l5_archEntries_eq_mapMatrix K g

private theorem e8l5_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [e8l5_of_archEntries, Units.val_mul, map_mul]

variable {K}

private def e8l5single (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

private theorem e8l5_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) :
    archMatrixUpdate K w m i j = archMatrixUpdate K w 0 i j + e8l5single w (m i j) := by
  funext v
  show archMatrixUpdate K w m i j v =
    archMatrixUpdate K w 0 i j v + Pi.single (M := fun v : InfinitePlace K => v.Completion) w (m i j) v
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self, archMatrixUpdate_apply_self, Pi.single_eq_same, Matrix.zero_apply, zero_add]
  · rw [archMatrixUpdate_apply_of_ne K w m i j hv, archMatrixUpdate_apply_of_ne K w 0 i j hv, Pi.single_eq_of_ne hv,
      add_zero]

private def e8l5Const (w : InfinitePlace K) : e8l5Ent K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

private theorem e8l5_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      e8l5Const w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (e8l5single w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [e8l5_archMatrixUpdate_entry, map_add]
  rfl

private def e8l5AddHom {w : InfinitePlace K} (hw : w.IsComplex) : ℂ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivComplexOfIsComplex hw).symm.toAddMonoidHom)

private theorem e8l5AddHom_apply {w : InfinitePlace K} (hw : w.IsComplex) (r : ℂ) :
    e8l5AddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (e8l5single w ((ringEquivComplexOfIsComplex hw).symm r)) :=
  rfl

private theorem e8l5_continuous_addHom {w : InfinitePlace K} (hw : w.IsComplex) : Continuous (e8l5AddHom hw) := by
  have h1 : Continuous fun x : w.Completion => e8l5single w x := continuous_single w
  have h2 : Continuous fun r : ℂ => (ringEquivComplexOfIsComplex hw).symm r :=
    (isometryEquivComplexOfIsComplex hw).symm.continuous
  have h3 : ⇑(e8l5AddHom hw) = fun r : ℂ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (e8l5single w ((ringEquivComplexOfIsComplex hw).symm r)) :=
    funext fun r => e8l5AddHom_apply hw r
  rw [h3]
  exact (e8l5_continuous_ringEquiv K).comp (h1.comp h2)

private def e8l5Lin {w : InfinitePlace K} (hw : w.IsComplex) : ℂ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (e8l5AddHom hw).toRealLinearMap (e8l5_continuous_addHom hw)

private def e8l5LinMat {w : InfinitePlace K} (hw : w.IsComplex) : (Fin 2 → Fin 2 → ℂ) →L[ℝ] e8l5Ent K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (e8l5Lin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i))

private theorem e8l5LinMat_apply {w : InfinitePlace K} (hw : w.IsComplex) (e : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    e8l5LinMat hw e i j = e8l5AddHom hw (e i j) :=
  rfl

end FieldOnly

section NumberFieldPart

variable {K : Type} [Field K] [NumberField K]

private theorem e8l5_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (he : (Matrix.of e).det ≠ 0) :
    archEntries K (glArch (𝓞 K) K (archComplexLiftAt hw e)) = e8l5Const w + e8l5LinMat hw e := by
  rw [archComplexLiftAt_of_det_ne_zero hw he]
  have h1 : glArch (𝓞 K) K (archComplexGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) :=
    glArch_adelicArchGLIncl K _
  rw [h1]
  funext i j
  rw [e8l5_archEntries_archGLIncl, glEquivOfRingEquiv_apply_entry, Pi.add_apply, Pi.add_apply, e8l5LinMat_apply,
    e8l5AddHom_apply]
  rfl

end NumberFieldPart

end AffineData

section TestData

open MeasureTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem e8l5_glFin_lift (hw : w.IsComplex) {e : E8Ent} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archComplexLiftAt hw e) = 1 := by
  rw [archComplexLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

private theorem e8l5_glFin_archComplexGLAt (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    glFin (𝓞 K) K (archComplexGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl K _

private def e8l5MulRLin (M : e8l5Ent K) : e8l5Ent K →ₗ[ℝ] e8l5Ent K where
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

private def e8l5MulR (M : e8l5Ent K) : e8l5Ent K →L[ℝ] e8l5Ent K := LinearMap.toContinuousLinearMap (e8l5MulRLin M)

private theorem e8l5MulR_apply (M N : e8l5Ent K) : e8l5MulR M N = Matrix.of.symm (Matrix.of N * Matrix.of M) := rfl

private def e8l5MulRL : e8l5Ent K →ₗ[ℝ] (e8l5Ent K →L[ℝ] e8l5Ent K) where
  toFun := e8l5MulR
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

private theorem e8l5_continuous_mulR : Continuous (e8l5MulR : e8l5Ent K → e8l5Ent K →L[ℝ] e8l5Ent K) :=
  (e8l5MulRL (K := K)).continuous_of_finiteDimensional

private def e8l5MulLLin (A : e8l5Ent K) : e8l5Ent K →ₗ[ℝ] e8l5Ent K where
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

private def e8l5MulL (A : e8l5Ent K) : e8l5Ent K →L[ℝ] e8l5Ent K := LinearMap.toContinuousLinearMap (e8l5MulLLin A)

private theorem e8l5MulL_apply (A N : e8l5Ent K) : e8l5MulL A N = Matrix.of.symm (Matrix.of A * Matrix.of N) := rfl

private theorem e8l5_archEntries_lift_mul (hw : w.IsComplex) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (archComplexLiftAt hw e * y)) =
      e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
        e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw e) := by
  rw [e8l5MulR_apply, e8l5MulR_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (archComplexLiftAt hw e * y))), map_mul,
    e8l5_archEntries_mul, e8l5_archEntries_glArch_lift hw he]
  show Matrix.of.symm ((Matrix.of (e8l5Const w) + Matrix.of (e8l5LinMat hw e)) *
    Matrix.of (archEntries K (glArch (𝓞 K) K y))) = _
  rw [Matrix.add_mul]
  rfl

private theorem e8l5_factor_lift_mul (hw : w.IsComplex) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (archComplexLiftAt hw e * y) =
      Φ (e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
          e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, e8l5_archEntries_lift_mul hw he, map_mul, e8l5_glFin_lift hw he, one_mul]

open scoped Classical in

private theorem e8l5_isFactorizableTestFn_archComplexGLAt_mul (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K fun y => α (archComplexGLAt hw m * y) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hfa_supp⟩, hff, hαeq⟩ := hα
  refine ⟨fun z => fa (glArch (𝓞 K) K (archComplexGLAt hw m) * z), ff,
    ⟨⟨fun N => Φ (e8l5MulL (archEntries K (glArch (𝓞 K) K (archComplexGLAt hw m))) N), ?_, ?_⟩, ?_⟩, hff, ?_⟩
  · exact hΦ.comp (e8l5MulL (archEntries K (glArch (𝓞 K) K (archComplexGLAt hw m)))).contDiff
  · intro z
    beta_reduce
    rw [hfa, e8l5MulL_apply]
    congr 1
    rw [← e8l5_archEntries_mul]
    exact (Matrix.of.symm_apply_apply _).symm
  · exact hfa_supp.comp_homeomorph (Homeomorph.mulLeft (glArch (𝓞 K) K (archComplexGLAt hw m)))
  · intro y
    beta_reduce
    rw [hαeq, map_mul, map_mul, e8l5_glFin_archComplexGLAt hw m, one_mul]

private theorem e8l5_exists_compact_support (hw : w.IsComplex) {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : HasCompactSupport α)
    {S : Set E8Ent} (hS : IsCompact S) (hSd : S ⊆ e8DetSet) :
    ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ e' ∈ S, ∀ y ∉ C, α (archComplexLiftAt hw e' * y) = 0 := by
  have hS' : IsCompact (e8Inv '' S) := hS.image_of_continuousOn (e8tc_contDiffOn_tcInv.continuousOn.mono hSd)
  have hS'd : e8Inv '' S ⊆ e8DetSet := by
    rintro _ ⟨e', he', rfl⟩
    exact e8tc_tcInv_mem (hSd he')
  have hcont : ContinuousOn (fun p : E8Ent × AdelicGL2 (𝓞 K) K => archComplexLiftAt hw p.1 * p.2)
      ((e8Inv '' S) ×ˢ tsupport α) :=
    ((e8l5_continuousOn_lift hw).comp continuousOn_fst fun p hp => hS'd hp.1).mul continuousOn_snd
  refine ⟨(fun p : E8Ent × AdelicGL2 (𝓞 K) K => archComplexLiftAt hw p.1 * p.2) '' ((e8Inv '' S) ×ˢ tsupport α),
    (hS'.prod (hα : IsCompact (tsupport α))).image_of_continuousOn hcont, ?_⟩
  · intro e' he' y hy
    by_contra hne
    apply hy
    refine ⟨(e8Inv e', archComplexLiftAt hw e' * y), ⟨⟨e', he', rfl⟩, subset_tsupport _ hne⟩, ?_⟩
    show archComplexLiftAt hw (e8Inv e') * (archComplexLiftAt hw e' * y) = y
    rw [← e8l5_lift_inv hw (hSd he'), inv_mul_cancel_left]

end TestData

section Conv

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def e8leftDeriv (hw : w.IsComplex) (d : ArchDirComplex) (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0

private theorem e8l5_archFlowAtComplex_inv (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    (archFlowAtComplex hw d t : AdelicGL2 (𝓞 K) K)⁻¹ = archFlowAtComplex hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAtComplex_add, add_neg_cancel, archFlowAtComplex_zero])

private def e8l5Curve (d : ArchDirComplex) (t : ℝ) : E8Ent :=
  Matrix.of.symm
    (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ))

private theorem e8l5_curve_mem (d : ArchDirComplex) (t : ℝ) : e8l5Curve d t ∈ e8DetSet := by
  show (Matrix.of (e8l5Curve d t)).det ≠ 0
  rw [e8l5Curve, Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrixComplex d t).isUnit).ne_zero

private theorem e8l5_hasDerivAt_curve (d : ArchDirComplex) :
    HasDerivAt (e8l5Curve d)
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) * archDirMatrixComplex d)) 0 :=
  hasDerivAt_of_symm_mul_archFlowMatrixComplex _ d

private theorem e8l5_archFlowAtComplex_eq_lift (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    (archFlowAtComplex hw d t : AdelicGL2 (𝓞 K) K) = archComplexLiftAt hw (e8l5Curve d t) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [e8l5Curve, ← archComplexLiftAt_mul_archComplexGLAt hw hdet, archComplexLiftAt_of_symm_one, one_mul, archFlowAtComplex]

private def e8l5M (y : AdelicGL2 (𝓞 K) K) : e8l5Ent K := archEntries K (glArch (𝓞 K) K y)

private theorem e8l5_continuous_M : Continuous (e8l5M : AdelicGL2 (𝓞 K) K → e8l5Ent K) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => archEntries K (glArch (𝓞 K) K y)
  exact (e8l5_continuous_archEntries K).comp (continuous_glArch (𝓞 K) K)

private def e8l5cD (w : InfinitePlace K) (y : AdelicGL2 (𝓞 K) K) : e8l5Ent K := e8l5MulR (e8l5M y) (e8l5Const w)

private def e8l5LD (hw : w.IsComplex) (y : AdelicGL2 (𝓞 K) K) : E8Ent →L[ℝ] e8l5Ent K := (e8l5MulR (e8l5M y)).comp (e8l5LinMat hw)

private theorem e8l5_continuous_cD (w : InfinitePlace K) : Continuous (e8l5cD w) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => e8l5MulR (e8l5M y) (e8l5Const w)
  exact (e8l5_continuous_mulR.comp e8l5_continuous_M).clm_apply continuous_const

private theorem e8l5_continuous_LD (hw : w.IsComplex) : Continuous (e8l5LD (K := K) hw) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => (e8l5MulR (e8l5M y)).comp (e8l5LinMat hw)
  exact (e8l5_continuous_mulR.comp e8l5_continuous_M).clm_comp continuous_const

end Conv

section LeftDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def e8l5Dir (d : ArchDirComplex) : E8Ent :=
  (-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) * archDirMatrixComplex d)

private theorem e8l5_hasDerivAt_curve_neg (d : ArchDirComplex) : HasDerivAt (fun t : ℝ => e8l5Curve d (-t)) (e8l5Dir d) 0 := by
  have h := e8l5_hasDerivAt_curve d
  rw [← neg_zero] at h
  exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

private theorem e8l5_curve_det (d : ArchDirComplex) (t : ℝ) : (Matrix.of (e8l5Curve d t)).det ≠ 0 := e8l5_curve_mem d t

private theorem e8l5MulR_eq_mulL (N X : e8l5Ent K) : e8l5MulR N X = e8l5MulL X N := rfl

private def e8l5Phi' (hw : w.IsComplex) (d : ArchDirComplex) (Φ : e8l5Ent K → ℂ) (N : e8l5Ent K) : ℂ :=
  fderiv ℝ Φ (e8l5MulL (e8l5Const w) N + e8l5MulL (e8l5LinMat hw (e8l5Curve d (-0))) N) (e8l5MulL (e8l5LinMat hw (e8l5Dir d)) N)

private theorem e8l5_contDiff_Phi' (hw : w.IsComplex) (d : ArchDirComplex) {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (e8l5Phi' hw d Φ) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2.comp
    ((e8l5MulL (e8l5Const w)).contDiff.add (e8l5MulL (e8l5LinMat hw (e8l5Curve d (-0)))).contDiff)).clm_apply
    (e8l5MulL (e8l5LinMat hw (e8l5Dir d))).contDiff

private theorem e8l5_hasDerivAt_Phi_curve (hw : w.IsComplex) (d : ArchDirComplex) {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (N : e8l5Ent K) :
    HasDerivAt (fun t : ℝ => Φ (e8l5MulR N (e8l5Const w) + e8l5MulR N (e8l5LinMat hw (e8l5Curve d (-t)))))
      (e8l5Phi' hw d Φ N) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => e8l5LinMat hw (e8l5Curve d (-t))) (e8l5LinMat hw (e8l5Dir d)) 0 :=
    (e8l5LinMat hw).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (e8l5_hasDerivAt_curve_neg d)
  have h2 : HasDerivAt (fun t : ℝ => e8l5MulR N (e8l5LinMat hw (e8l5Curve d (-t)))) (e8l5MulR N (e8l5LinMat hw (e8l5Dir d))) 0 :=
    (e8l5MulR N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => e8l5MulR N (e8l5Const w) + e8l5MulR N (e8l5LinMat hw (e8l5Curve d (-t))))
      (e8l5MulR N (e8l5LinMat hw (e8l5Dir d))) 0 :=
    h2.const_add (e8l5MulR N (e8l5Const w))
  have h4 := ((contDiff_infty_iff_fderiv.1 hΦ).1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [e8l5Phi', ← e8l5MulR_eq_mulL]
  exact h4

private theorem e8l5_fa_lift_mul (hw : w.IsComplex) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {Φ : e8l5Ent K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    fa (glArch (𝓞 K) K (archComplexLiftAt hw e) * z) =
      Φ (e8l5MulR (archEntries K z) (e8l5Const w) + e8l5MulR (archEntries K z) (e8l5LinMat hw e)) := by
  rw [hfa, ← map_add, e8l5MulR_apply, ← e8l5_archEntries_glArch_lift hw he, ← e8l5_archEntries_mul, Equiv.symm_apply_apply]

private theorem e8l5_glFin_archFlowAtComplex (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    glFin (𝓞 K) K (archFlowAtComplex hw d t) = 1 := by
  rw [e8l5_archFlowAtComplex_eq_lift]
  exact e8l5_glFin_lift hw (e8l5_curve_det d t)

private theorem e8l5_leftDeriv_eq (hw : w.IsComplex) (d : ArchDirComplex) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (y : AdelicGL2 (𝓞 K) K) :
    e8leftDeriv hw d α y = e8l5Phi' hw d Φ (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  have hfun : (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) = fun t : ℝ =>
      Φ (e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
          e8l5MulR (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw (e8l5Curve d (-t)))) *
        ff (glFin (𝓞 K) K y) := by
    funext t
    rw [e8l5_archFlowAtComplex_eq_lift, e8l5_factor_lift_mul hw hfa hα (e8l5_curve_det d (-t)) y]
  show deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0 = _
  rw [hfun]
  exact ((e8l5_hasDerivAt_Phi_curve hw d hΦ _).mul_const _).deriv

private theorem e8l5_hasCompactSupport_Phi' (hw : w.IsComplex) (d : ArchDirComplex) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) : HasCompactSupport fun z => e8l5Phi' hw d Φ (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  simp only [Function.mem_support] at hz
  by_contra hzt
  apply hz

  have hcurve : ContinuousAt (fun t : ℝ => e8l5Curve d (-t)) 0 := (e8l5_hasDerivAt_curve_neg d).continuousAt
  have hlift : ContinuousAt (fun t : ℝ => (archComplexLiftAt hw (e8l5Curve d (-t)) : AdelicGL2 (𝓞 K) K)) 0 :=
    ContinuousAt.comp_of_eq
      ((e8l5_continuousOn_lift hw).continuousAt (e8tc_isOpen_detSet.mem_nhds (e8l5_curve_mem d (-0)))) hcurve rfl
  have horbit : ContinuousAt (fun t : ℝ => glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-t))) * z) 0 :=
    ((continuous_glArch (𝓞 K) K).continuousAt.comp hlift).mul continuousAt_const
  have hz0 : glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-0)) : AdelicGL2 (𝓞 K) K) * z = z := by
    rw [← e8l5_archFlowAtComplex_eq_lift, neg_zero, archFlowAtComplex_zero, map_one, one_mul]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, fa (glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-t))) * z) = 0 := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-0)) : AdelicGL2 (𝓞 K) K) * z) := by
      rw [hz0]
      exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hzt
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hfun : (fun t : ℝ => fa (glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-t))) * z)) = fun t : ℝ =>
      Φ (e8l5MulR (archEntries K z) (e8l5Const w) + e8l5MulR (archEntries K z) (e8l5LinMat hw (e8l5Curve d (-t)))) := by
    funext t
    exact e8l5_fa_lift_mul hw hfa (e8l5_curve_det d (-t)) z
  have hd : HasDerivAt (fun t : ℝ => fa (glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-t))) * z))
      (e8l5Phi' hw d Φ (archEntries K z)) 0 := by
    rw [hfun]
    exact e8l5_hasDerivAt_Phi_curve hw d hΦ (archEntries K z)
  have heq : (fun t : ℝ => fa (glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d (-t))) * z)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => (0 : ℂ) :=
    hev.mono fun t ht => ht
  rw [← hd.deriv, heq.deriv_eq, deriv_const]

private theorem e8l5_isFactorizableTestFn_leftDeriv (hw : w.IsComplex) (d : ArchDirComplex) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) : IsFactorizableTestFn K (e8leftDeriv hw d α) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩ := hα
  exact ⟨fun z => e8l5Phi' hw d Φ (archEntries K z), ff,
    ⟨⟨e8l5Phi' hw d Φ, e8l5_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, e8l5_hasCompactSupport_Phi' hw d hΦ hfa hsupp⟩, hff,
    e8l5_leftDeriv_eq hw d hΦ hfa hαeq⟩

private theorem e8l5_leftDeriv_tensor (hw : w.IsComplex) (d : ArchDirComplex) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
      e8leftDeriv hw d (fun z => fa (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z)) =
        fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨fun z => e8l5Phi' hw d Φ (archEntries K z),
    ⟨⟨e8l5Phi' hw d Φ, e8l5_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, e8l5_hasCompactSupport_Phi' hw d hΦ hfaΦ hsupp⟩, ?_⟩
  funext y
  exact e8l5_leftDeriv_eq hw d hΦ hfaΦ (fun _ => rfl) y

end LeftDerivFactor

section RightDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def e8r5Dir (d : ArchDirComplex) : E8Ent :=
  Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) * archDirMatrixComplex d)

private theorem e8r5_hasDerivAt_curve (d : ArchDirComplex) : HasDerivAt (e8l5Curve d) (e8r5Dir d) 0 :=
  e8l5_hasDerivAt_curve d

private theorem e8r5_archEntries_mul_lift (hw : w.IsComplex) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (y * archComplexLiftAt hw e)) =
      e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
        e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw e) := by
  rw [e8l5MulL_apply, e8l5MulL_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (y * archComplexLiftAt hw e))), map_mul,
    e8l5_archEntries_mul, e8l5_archEntries_glArch_lift hw he]
  show Matrix.of.symm (Matrix.of (archEntries K (glArch (𝓞 K) K y)) *
    (Matrix.of (e8l5Const w) + Matrix.of (e8l5LinMat hw e))) = _
  rw [Matrix.mul_add]
  rfl

private theorem e8r5_factor_mul_lift (hw : w.IsComplex) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (y * archComplexLiftAt hw e) =
      Φ (e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
          e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, e8r5_archEntries_mul_lift hw he, map_mul, e8l5_glFin_lift hw he, mul_one]

private theorem e8r5_fa_mul_lift (hw : w.IsComplex) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {Φ : e8l5Ent K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) {e : E8Ent} (he : (Matrix.of e).det ≠ 0)
    (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    fa (z * glArch (𝓞 K) K (archComplexLiftAt hw e)) =
      Φ (e8l5MulL (archEntries K z) (e8l5Const w) + e8l5MulL (archEntries K z) (e8l5LinMat hw e)) := by
  rw [hfa, ← map_add, e8l5MulL_apply, ← e8l5_archEntries_glArch_lift hw he, ← e8l5_archEntries_mul, Equiv.symm_apply_apply]

private theorem e8r5_isArchSmoothAt (hw : w.IsComplex) {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAtComplex hw α := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, -, hαeq⟩ := hα
  intro g
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : E8Ent =>
      Φ (e8l5MulL (archEntries K (glArch (𝓞 K) K g)) (e8l5Const w) +
          e8l5MulL (archEntries K (glArch (𝓞 K) K g)) (e8l5LinMat hw e)) * ff (glFin (𝓞 K) K g)) e8DetSet :=
    ((hΦ.comp (contDiff_const.add ((e8l5MulL (archEntries K (glArch (𝓞 K) K g))).contDiff.comp
      (e8l5LinMat hw).contDiff))).mul contDiff_const).contDiffOn
  refine hsm.congr fun e he => ?_
  exact e8r5_factor_mul_lift hw hfa hαeq he g

private def e8r5Phi' (hw : w.IsComplex) (d : ArchDirComplex) (Φ : e8l5Ent K → ℂ) (N : e8l5Ent K) : ℂ :=
  fderiv ℝ Φ (e8l5MulR (e8l5Const w) N + e8l5MulR (e8l5LinMat hw (e8l5Curve d 0)) N) (e8l5MulR (e8l5LinMat hw (e8r5Dir d)) N)

private theorem e8r5_contDiff_Phi' (hw : w.IsComplex) (d : ArchDirComplex) {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (e8r5Phi' hw d Φ) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2.comp
    ((e8l5MulR (e8l5Const w)).contDiff.add (e8l5MulR (e8l5LinMat hw (e8l5Curve d 0))).contDiff)).clm_apply
    (e8l5MulR (e8l5LinMat hw (e8r5Dir d))).contDiff

private theorem e8r5_hasDerivAt_Phi_curve (hw : w.IsComplex) (d : ArchDirComplex) {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (N : e8l5Ent K) :
    HasDerivAt (fun t : ℝ => Φ (e8l5MulL N (e8l5Const w) + e8l5MulL N (e8l5LinMat hw (e8l5Curve d t))))
      (e8r5Phi' hw d Φ N) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => e8l5LinMat hw (e8l5Curve d t)) (e8l5LinMat hw (e8r5Dir d)) 0 :=
    (e8l5LinMat hw).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (e8r5_hasDerivAt_curve d)
  have h2 : HasDerivAt (fun t : ℝ => e8l5MulL N (e8l5LinMat hw (e8l5Curve d t))) (e8l5MulL N (e8l5LinMat hw (e8r5Dir d))) 0 :=
    (e8l5MulL N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => e8l5MulL N (e8l5Const w) + e8l5MulL N (e8l5LinMat hw (e8l5Curve d t)))
      (e8l5MulL N (e8l5LinMat hw (e8r5Dir d))) 0 :=
    h2.const_add (e8l5MulL N (e8l5Const w))
  have h4 := ((contDiff_infty_iff_fderiv.1 hΦ).1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [e8r5Phi', e8l5MulR_eq_mulL]
  exact h4

private theorem e8r5_archDerivAtComplex_eq (hw : w.IsComplex) (d : ArchDirComplex) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (y : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d α y = e8r5Phi' hw d Φ (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  have hfun : (fun t : ℝ => α (y * archFlowAtComplex hw d t)) = fun t : ℝ =>
      Φ (e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5Const w) +
          e8l5MulL (archEntries K (glArch (𝓞 K) K y)) (e8l5LinMat hw (e8l5Curve d t))) *
        ff (glFin (𝓞 K) K y) := by
    funext t
    rw [e8l5_archFlowAtComplex_eq_lift, e8r5_factor_mul_lift hw hfa hα (e8l5_curve_det d t) y]
  show deriv (fun t : ℝ => α (y * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  exact ((e8r5_hasDerivAt_Phi_curve hw d hΦ _).mul_const _).deriv

private theorem e8r5_hasCompactSupport_Phi' (hw : w.IsComplex) (d : ArchDirComplex) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {Φ : e8l5Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) : HasCompactSupport fun z => e8r5Phi' hw d Φ (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  simp only [Function.mem_support] at hz
  by_contra hzt
  apply hz
  have hcurve : ContinuousAt (fun t : ℝ => e8l5Curve d t) 0 := (e8r5_hasDerivAt_curve d).continuousAt
  have hlift : ContinuousAt (fun t : ℝ => (archComplexLiftAt hw (e8l5Curve d t) : AdelicGL2 (𝓞 K) K)) 0 :=
    ContinuousAt.comp_of_eq
      ((e8l5_continuousOn_lift hw).continuousAt (e8tc_isOpen_detSet.mem_nhds (e8l5_curve_mem d 0))) hcurve rfl
  have horbit : ContinuousAt (fun t : ℝ => z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d t))) 0 :=
    continuousAt_const.mul ((continuous_glArch (𝓞 K) K).continuousAt.comp hlift)
  have hz0 : z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d 0) : AdelicGL2 (𝓞 K) K) = z := by
    rw [← e8l5_archFlowAtComplex_eq_lift, archFlowAtComplex_zero, map_one, mul_one]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, fa (z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d t))) = 0 := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d 0) : AdelicGL2 (𝓞 K) K)) := by
      rw [hz0]
      exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hzt
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hfun : (fun t : ℝ => fa (z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d t)))) = fun t : ℝ =>
      Φ (e8l5MulL (archEntries K z) (e8l5Const w) + e8l5MulL (archEntries K z) (e8l5LinMat hw (e8l5Curve d t))) := by
    funext t
    exact e8r5_fa_mul_lift hw hfa (e8l5_curve_det d t) z
  have hd : HasDerivAt (fun t : ℝ => fa (z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d t))))
      (e8r5Phi' hw d Φ (archEntries K z)) 0 := by
    rw [hfun]
    exact e8r5_hasDerivAt_Phi_curve hw d hΦ (archEntries K z)
  have heq : (fun t : ℝ => fa (z * glArch (𝓞 K) K (archComplexLiftAt hw (e8l5Curve d t)))) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => (0 : ℂ) :=
    hev.mono fun t ht => ht
  rw [← hd.deriv, heq.deriv_eq, deriv_const]

private theorem e8r5_main (hw : w.IsComplex) (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAtComplex hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDirComplex, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAtComplex hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
  refine ⟨e8r5_isArchSmoothAt hw hα, ?_⟩
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩ := hα
  exact ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq, fun d =>
    ⟨fun z => e8r5Phi' hw d Φ (archEntries K z),
      ⟨⟨e8r5Phi' hw d Φ, e8r5_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, e8r5_hasCompactSupport_Phi' hw d hΦ hfa hsupp⟩,
      fun y => e8r5_archDerivAtComplex_eq hw d hΦ hfa hαeq y⟩⟩

end RightDerivFactor

end

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAtComplex hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDirComplex, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAtComplex hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) :=
  e8r5_main hw α hα

end S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
end P2MW
export P2MW.S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor (solution)
