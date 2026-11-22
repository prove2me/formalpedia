-- Prove2me | Definitions.Def_MegiddoLP_HyperplaneSlice
-- name    : MegiddoLP_HyperplaneSlice
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:10:39.285101+00:00
-- url     : https://prove2.me/theorems/af692081-73bd-4dae-bc0e-128105125306
-- title:
--   Eliminate a coordinate on a hyperplane in linear programming
-- statement:
--   Substituting for a nonzero pivot coordinate reduces a hyperplane-restricted linear program by one variable. The reduced system preserves feasibility and the objective up to a constant.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §4, pp. 123–124. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_Polyhedron
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Ring

namespace MegiddoLP.FixedDim

open Matrix LinearOptimization

/-- Solve the hyperplane equation for its first coordinate. A different nonzero
pivot coordinate can be moved to the first slot by permuting coordinates. -/
noncomputable def liftToHyperplane {d : ℕ} (normal : Fin (d + 1) → ℝ)
    (rhs : ℝ) (y : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons ((rhs - Fin.tail normal ⬝ᵥ y) / normal 0) y

/-- Substitute the eliminated coordinate in a row or objective. -/
noncomputable def sliceRow {d : ℕ} (normal row : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  Fin.tail row - (row 0 / normal 0) • Fin.tail normal

theorem dotProduct_liftToHyperplane {d : ℕ} {normal : Fin (d + 1) → ℝ}
    (hpivot : normal 0 ≠ 0) (row : Fin (d + 1) → ℝ) (rhs : ℝ) (y : Fin d → ℝ) :
    row ⬝ᵥ liftToHyperplane normal rhs y =
      row 0 / normal 0 * rhs + sliceRow normal row ⬝ᵥ y := by
  have hrow :
      sliceRow normal row ⬝ᵥ y = Fin.tail row ⬝ᵥ y -
        row 0 / normal 0 * (Fin.tail normal ⬝ᵥ y) := by
    simp [sliceRow, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hrow]
  change row ⬝ᵥ Matrix.vecCons ((rhs - Fin.tail normal ⬝ᵥ y) / normal 0) y = _
  rw [Matrix.dotProduct_cons]
  change row 0 * ((rhs - Fin.tail normal ⬝ᵥ y) / normal 0) +
    Fin.tail row ⬝ᵥ y = _
  field_simp
  ring

theorem liftToHyperplane_mem {d : ℕ} {normal : Fin (d + 1) → ℝ}
    (hpivot : normal 0 ≠ 0) (rhs : ℝ) (y : Fin d → ℝ) :
    normal ⬝ᵥ liftToHyperplane normal rhs y = rhs := by
  rw [dotProduct_liftToHyperplane hpivot]
  simp [sliceRow, hpivot]

theorem liftToHyperplane_tail {d : ℕ} {normal x : Fin (d + 1) → ℝ} {rhs : ℝ}
    (hpivot : normal 0 ≠ 0) (hx : normal ⬝ᵥ x = rhs) :
    liftToHyperplane normal rhs (Fin.tail x) = x := by
  have hg : normal 0 * x 0 + Fin.tail normal ⬝ᵥ Fin.tail x = rhs := by
    nth_rw 1 [← Fin.cons_self_tail x] at hx
    change normal ⬝ᵥ Matrix.vecCons (x 0) (Fin.tail x) = rhs at hx
    rw [Matrix.dotProduct_cons] at hx
    exact hx
  have hhead : (rhs - Fin.tail normal ⬝ᵥ Fin.tail x) / normal 0 = x 0 :=
    (div_eq_iff hpivot).2 (by linarith)
  rw [liftToHyperplane, hhead, Fin.cons_self_tail]

/-- The feasibility subproblem on a query hyperplane has one fewer column
and exactly the same number of inequalities. -/
theorem hyperplane_feasible_iff {n d : ℕ} {normal : Fin (d + 1) → ℝ}
    (hpivot : normal 0 ≠ 0) (rhs : ℝ)
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ) :
    (∃ x ∈ polyhedron A b, normal ⬝ᵥ x = rhs) ↔
      (polyhedron (fun i => sliceRow normal (A i))
        (fun i => b i - A i 0 / normal 0 * rhs)).Nonempty := by
  have hrow (y : Fin d → ℝ) (i : Fin n) :
      b i ≤ (A *ᵥ liftToHyperplane normal rhs y) i ↔
        b i - A i 0 / normal 0 * rhs ≤ sliceRow normal (A i) ⬝ᵥ y := by
    rw [Matrix.mulVec, dotProduct_liftToHyperplane hpivot]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨x, hx, hxH⟩
    refine ⟨Fin.tail x, fun i => (hrow (Fin.tail x) i).mp ?_⟩
    simpa only [liftToHyperplane_tail hpivot hxH] using hx i
  · rintro ⟨y, hy⟩
    exact ⟨liftToHyperplane normal rhs y, fun i => (hrow y i).mpr (hy i),
      liftToHyperplane_mem hpivot rhs y⟩

end MegiddoLP.FixedDim


