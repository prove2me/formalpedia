-- Prove2me | solution 1 for Auto.re_trace_sylvSol_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:16.391417+00:00
-- url     : https://prove2.me/submissions/012d40f5-e6a9-4578-8b1f-0df3931a8adc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_eigenvalues_pos
public import Theorems.Thm_Auto_matCostBil_eq
public import Theorems.Thm_Auto_eigCoord_sylvSol

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {Y K G : Matrix n n ℂ} (hY : Y.PosDef) (hG : G.IsHermitian) :
    (3 / 2) * ((sylvSol (CFC.sqrt Y) K * G).trace).re = matCostBil Y K G := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = hY.1.eigenvectorUnitary := ⟨_, rfl⟩
  have hE : ∀ Z, eigCoord hY.1 Z = star (U : Matrix n n ℂ) * Z * (U : Matrix n n ℂ) := by
    intro Z; rw [hUdef]; rfl
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  set X := sylvSol (CFC.sqrt Y) K
  have htr : (X * G).trace = (eigCoord hY.1 X * eigCoord hY.1 G).trace := by
    rw [hE, hE]
    calc (X * G).trace = (star (U : Matrix n n ℂ) * (X * G) * U).trace := by
          rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
      _ = _ := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (U : Matrix n n ℂ), hUU, Matrix.one_mul]
  have hGt : ∀ i j, eigCoord hY.1 G j i = star (eigCoord hY.1 G i j) := by
    intro i j
    have hH : (eigCoord hY.1 G).IsHermitian := by
      rw [hE, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hG.eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    exact (hH.apply j i).symm
  rw [htr, matCostBil_eq hY, Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eigCoord_sylvSol hY K i j, hGt i j]
  set c := √(hY.1.eigenvalues i) + √(hY.1.eigenvalues j)
  set k := eigCoord hY.1 K i j
  set g := eigCoord hY.1 G i j
  have hcne : c ≠ 0 := (add_pos (sqrt_eigenvalues_pos hY i) (sqrt_eigenvalues_pos hY j)).ne'
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  have e : k / (c : ℂ) * star g = ((1 / c : ℝ) : ℂ) * (k * star g) := by
    push_cast; field_simp
  have e2 : (k * star g).re = ((starRingEnd ℂ) k * g).re := by
    rw [RCLike.star_def, ← Complex.conj_re]; simp [mul_comm]
  rw [e, Complex.re_ofReal_mul, e2]
  field_simp
end Auto
