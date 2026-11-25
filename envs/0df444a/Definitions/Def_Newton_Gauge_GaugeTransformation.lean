-- Prove2me | Definitions.Def_Newton_Gauge_GaugeTransformation
-- name    : Newton_Gauge_GaugeTransformation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:28.629171+00:00
-- url     : https://prove2.me/theorems/0667b7b8-f0a0-4c1f-bf6b-596dbf35280a
-- title:
--   Gauge Transformation
-- statement:
--   Definitions and structural lemmas for Gauge Transformation, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_Newton_Gauge_LieAlgebra
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


set_option autoImplicit false
open Matrix
namespace Newton
variable {N : ℕ}
structure SUNGroup (N : ℕ) where
  /-- Matrix representation -/
  matrix : Matrix (Fin N) (Fin N) ℂ
  /-- Unitary condition: g g† = 1 -/
  unitary : matrix * conjTranspose matrix = 1
  /-- Special condition: det(g) = 1 -/
  det_one : det matrix = 1
namespace SUNGroup
theorem ext {g h : SUNGroup N} (hm : g.matrix = h.matrix) : g = h := by
  cases g; cases h; simp_all
theorem unitary' (g : SUNGroup N) :
    conjTranspose g.matrix * g.matrix = 1 := by
  -- For unitary matrices, g g† = 1 ⟺ g† g = 1
  -- Since det g = 1 ≠ 0, g is invertible
  have h_isUnit : IsUnit (det g.matrix) := by
    rw [g.det_one]; exact isUnit_one
  have h_inv : g.matrix⁻¹ = conjTranspose g.matrix := by
    -- From g g† = 1, we get g⁻¹ = g†
    exact inv_eq_right_inv g.unitary
  -- g† g = g⁻¹ g = 1
  rw [← h_inv]
  exact nonsing_inv_mul g.matrix h_isUnit
instance : One (SUNGroup N) where
  one := {
    matrix := 1
    unitary := by simp [conjTranspose_one]
    det_one := by simp
  }
instance : Mul (SUNGroup N) where
  mul g h := {
    matrix := g.matrix * h.matrix
    unitary := by
      rw [conjTranspose_mul]
      calc (g.matrix * h.matrix) * (conjTranspose h.matrix * conjTranspose g.matrix)
          = g.matrix * (h.matrix * conjTranspose h.matrix) * conjTranspose g.matrix := by
            simp only [Matrix.mul_assoc]
        _ = g.matrix * 1 * conjTranspose g.matrix := by rw [h.unitary]
        _ = g.matrix * conjTranspose g.matrix := by rw [mul_one]
        _ = 1 := g.unitary
    det_one := by
      rw [det_mul, g.det_one, h.det_one, one_mul]
  }
noncomputable instance : Inv (SUNGroup N) where
  inv g := {
    matrix := conjTranspose g.matrix
    unitary := by
      rw [conjTranspose_conjTranspose]
      exact g.unitary'
    det_one := by
      rw [det_conjTranspose]
      simp only [g.det_one, star_one]
  }
@[simp]
theorem one_matrix : (1 : SUNGroup N).matrix = 1 := rfl
@[simp]
theorem mul_matrix (g h : SUNGroup N) : (g * h).matrix = g.matrix * h.matrix := rfl
@[simp]
theorem inv_matrix (g : SUNGroup N) : g⁻¹.matrix = conjTranspose g.matrix := rfl
@[simp]
theorem mul_one (g : SUNGroup N) : g * 1 = g := by
  apply ext
  simp
@[simp]
theorem one_mul (g : SUNGroup N) : 1 * g = g := by
  apply ext
  simp
@[simp]
theorem mul_inv (g : SUNGroup N) : g * g⁻¹ = 1 := by
  apply ext
  simp only [mul_matrix, inv_matrix, one_matrix]
  exact g.unitary
@[simp]
theorem inv_mul (g : SUNGroup N) : g⁻¹ * g = 1 := by
  apply ext
  simp only [mul_matrix, inv_matrix, one_matrix]
  exact g.unitary'
theorem mul_assoc (g h k : SUNGroup N) : g * h * k = g * (h * k) := by
  apply ext
  simp only [mul_matrix]
  exact Matrix.mul_assoc _ _ _
end SUNGroup
noncomputable def adjointAction (g : SUNGroup N) (A : SuNAlgebra N) : SuNAlgebra N where
  matrix := g.matrix * A.matrix * conjTranspose g.matrix
  trace_zero := by
    -- Tr(gAg†) = Tr(g†gA) = Tr(A) = 0 (cyclicity of trace)
    have h1 : trace (g.matrix * A.matrix * conjTranspose g.matrix) =
        trace (conjTranspose g.matrix * g.matrix * A.matrix) := by
      rw [trace_mul_cycle, Matrix.mul_assoc]
    rw [h1, g.unitary', one_mul]
    exact A.trace_zero
  anti_hermitian := by
    -- (gAg†)† = (g†)† A† g† = g (-A) g† = -gAg†
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [A.anti_hermitian]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [Matrix.mul_assoc]
namespace adjointAction
end adjointAction
end Newton


