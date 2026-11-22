-- Prove2me | solution 1 for Auto.phi_sq_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:11.520885+00:00
-- url     : https://prove2.me/submissions/c0d6fdad-049b-4ca5-898d-b45f1507f41c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_edec_sq
public import Theorems.Thm_Auto_gdom_eq
public import Theorems.Thm_Auto_exp_pair_le
public import Theorems.Thm_Auto_sum_three_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution {σb τb : ℝ} (hσ : 0 < σb) (hτ : 0 < τb) (v : Fin 3) (p : Fin 3 → ℝ) :
    HeatData.phi σb v p ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ 4 * gdom (min (1 /
      (8 * σb)) (1 / (4 * τb)) / 4) p := by
  set E0 := edec σb (p v)
  set E1 := edec σb (p (v + 1))
  set E2 := edec σb (p (v - 1))
  set ε := min (1 / (8 * σb)) (1 / (4 * τb)) / 4
  have hx : 0 < 1 / (8 * σb) := by positivity
  have hy : 0 < 1 / (4 * τb) := by positivity
  obtain ⟨hs1, hs2, hq1, hq2⟩ := sum_three_eq v p
  have hG : Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) =
      Real.exp (-(p 0 + p 1 + p 2) ^ 2 * (1 / (4 * τb))) := by congr 1; ring
  have hE : ∀ x, edec σb x ^ 2 = Real.exp (-(x ^ 2) * (1 / (8 * σb))) := fun x => by
    rw [edec_sq]; congr 1; ring
  have t1 : (E0 * E1) ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ gdom ε p := by
    rw [mul_pow, hE, hE, ← Real.exp_add, hG, gdom_eq, hs1, hq1]
    have := exp_pair_le (p v) (p (v + 1)) (p (v - 1)) hx hy
    convert this using 2
    ring_nf
  have t2 : (E0 * E2) ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ gdom ε p := by
    rw [mul_pow, hE, hE, ← Real.exp_add, hG, gdom_eq, hs2, hq2]
    have := exp_pair_le (p v) (p (v - 1)) (p (v + 1)) hx hy
    convert this using 2
    ring_nf
  have hphi : HeatData.phi σb v p ^ 2 ≤ 2 * (E0 * E1) ^ 2 + 2 * (E0 * E2) ^ 2 := by
    simp only [HeatData.phi, E0, E1, E2]
    nlinarith [sq_nonneg (edec σb (p v) * edec σb (p (v + 1)) -
      edec σb (p v) * edec σb (p (v - 1)))]
  have hexp := (Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb))).le
  calc HeatData.phi σb v p ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb))
      ≤ (2 * (E0 * E1) ^ 2 + 2 * (E0 * E2) ^ 2) *
          Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) :=
        mul_le_mul_of_nonneg_right hphi hexp
    _ ≤ 4 * gdom ε p := by nlinarith
end Auto
