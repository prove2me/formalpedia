-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:33.733557+00:00
-- url     : https://prove2.me/theorems/4ac18a34-4806-5a3e-af92-7bc962c3987d
-- title:
--   Matrix Haar Right Translate
-- statement:
--   Definitions and structural lemmas for Matrix Haar Right Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
namespace GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
def rightMul (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F where
  toFun x := x * (g : Matrix (Fin m) (Fin m) F)
  invFun x := x * ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
  left_inv x := by beta_reduce; rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by beta_reduce; rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul x y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const
def leftMul {n : ℕ} (m : ℕ) (g : GL (Fin n) F) :
    Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F where
  toFun x := (g : Matrix (Fin n) (Fin n) F) * x
  invFun x := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * x
  left_inv x := by beta_reduce; rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv x := by beta_reduce; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ x y
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id
def dg {m : ℕ} : (Fin m → Fˣ) →* GL (Fin m) F where
  toFun u :=
    { val := Matrix.diagonal fun i => (u i : F)
      inv := Matrix.diagonal fun i => (((u i)⁻¹ : Fˣ) : F)
      val_inv := by simp [Matrix.diagonal_mul_diagonal]
      inv_val := by simp [Matrix.diagonal_mul_diagonal] }
  map_one' := by ext; simp [Matrix.one_apply, Matrix.diagonal_apply]
  map_mul' u v := by
    apply Units.ext
    simp [Matrix.diagonal_mul_diagonal]
def colLat (O : Subring F) (ϖ : F) (n : ℕ) {m : ℕ} (j : Fin m) : Set (Matrix (Fin n) (Fin m) F) :=
  {x | ∀ i b, x i b * (if b = j then ϖ else 1) ∈ O}
section Measure
variable [MeasurableSpace F] [BorelSpace F]
def scale (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) : ℝ≥0∞ :=
  ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n)
theorem det_pos (nrm : AbsoluteValue F ℝ) {m : ℕ} (g : GL (Fin m) F) :
    0 < nrm (g : Matrix (Fin m) (Fin m) F).det := by
  exact AbsoluteValue.pos (abv := nrm) (Matrix.isUnits_det_units g).ne_zero
theorem scale_mul (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g h : GL (Fin m) F) :
    scale nrm n (g * h) = scale nrm n g * scale nrm n h := by
  simp only [scale, Units.val_mul, Matrix.det_mul, map_mul, mul_inv, mul_pow]
  exact ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 (AbsoluteValue.nonneg nrm _)) _)
theorem scale_ne_zero (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g ≠ 0 := by
  rw [scale, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos (inv_pos.2 (det_pos nrm g)) n
theorem scale_ne_top (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g ≠ ⊤ := ENNReal.ofReal_ne_top
theorem scale_inv (nrm : AbsoluteValue F ℝ) (n : ℕ) {m : ℕ} (g : GL (Fin m) F) :
    scale nrm n g⁻¹ = (scale nrm n g)⁻¹ := by
  have hd := det_pos nrm g
  have h1 : nrm ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det *
      nrm (g : Matrix (Fin m) (Fin m) F).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one,
      AbsoluteValue.map_one]
  unfold scale
  rw [eq_inv_of_mul_eq_one_left h1, ← ENNReal.ofReal_inv_of_pos (pow_pos (inv_pos.2 hd) n)]
  congr 1
  exact inv_pow _ _
theorem measurable_rightMul {m : ℕ} (n : ℕ) [BorelSpace (Matrix (Fin n) (Fin m) F)]
    (g : GL (Fin m) F) : Measurable (rightMul n g : Matrix (Fin n) (Fin m) F → _) := by
  exact (continuous_id.matrix_mul continuous_const).measurable
def stab (nrm : AbsoluteValue F ℝ) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    (dx : Measure (Matrix (Fin n) (Fin m) F)) : Subgroup (GL (Fin m) F) where
  carrier := {g | Measure.map (rightMul n g) dx = scale nrm n g • dx}
  one_mem' := by
    have : (⇑(rightMul n (1 : GL (Fin m) F)) : _ → _) = id := by
      funext x; simp [rightMul]
    show Measure.map _ dx = _
    rw [this, Measure.map_id]
    simp [scale]
  mul_mem' := by
    intro g h hg hh
    have : (⇑(rightMul n (g * h)) : _ → _) = rightMul n h ∘ rightMul n g := by
      funext x; simp [rightMul, Matrix.mul_assoc]
    show Measure.map _ dx = _
    rw [this, ← Measure.map_map (measurable_rightMul n h) (measurable_rightMul n g), show Measure.map _ dx = _ from hg,
      Measure.map_smul, show Measure.map _ dx = _ from hh, smul_smul, scale_mul, mul_comm]
  inv_mem' := by
    intro g hg
    have hid : (⇑(rightMul n g⁻¹) ∘ ⇑(rightMul n g) : _ → _) = id := by
      funext x; simp [rightMul, Matrix.mul_assoc]
    have h2 : Measure.map (rightMul n g⁻¹) (Measure.map (rightMul n g) dx) = dx := by
      rw [Measure.map_map (measurable_rightMul n g⁻¹) (measurable_rightMul n g), hid, Measure.map_id]
    rw [show Measure.map _ dx = _ from hg, Measure.map_smul] at h2
    show Measure.map _ dx = _
    rw [scale_inv]
    conv_rhs => rw [← h2]
    rw [smul_smul, ENNReal.inv_mul_cancel (scale_ne_zero nrm n g) (scale_ne_top nrm n g), one_smul]
end Measure
end GlobalTheory.CompanionTheory.QLScale


