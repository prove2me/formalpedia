-- Prove2me | solution 1 for Auto.hasDerivAt_energyReg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:43:59.79661+00:00
-- url     : https://prove2.me/submissions/97fc523d-bea6-4108-aa9b-8fd287a5c3d7

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef
public import Theorems.Thm_Auto_hasDerivAt_sqrt_curve
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_add_smul_one_sub_posSemidef
public import Theorems.Thm_Auto_hasDerivAt_re_trace_mul
public import Theorems.Thm_Auto_energyReg_eq_trace

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
theorem _root_.solution {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hP : ∀ θ, (P θ).PosSemidef) (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀) :
    HasDerivAt (fun θ => energyReg η (P θ)) ((3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) *
      P').trace).re) θ₀ := by
  set Y : ℝ → Matrix n n ℂ := fun θ => P θ + (η : ℂ) • 1
  have hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (P' i j) θ₀ := by
    intro i j
    have := (hd i j).add_const (((η : ℂ) • (1 : Matrix n n ℂ)) i j)
    simpa [Y] using this
  have hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := fun θ =>
    add_smul_one_sub_posSemidef (hP θ) η
  have hA := hasDerivAt_sqrt_curve hη hpos hY
  set A0 := CFC.sqrt (Y θ₀)
  set X := sylvSol A0 P'
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have hXs : A0 * X + X * A0 = P' := (sylvSol_spec hs (sqrt_sub_posSemidef hη.le (hpos θ₀)) P').1
  have hT := hasDerivAt_re_trace_mul hY hA
  have heq : ∀ θ, energyReg η (P θ) = ((Y θ * CFC.sqrt (Y θ)).trace).re -
      η ^ (3 / 2 : ℝ) * Fintype.card n := fun θ => energyReg_eq_trace (hP θ) hη.le
  simp_rw [heq]
  refine (hT.sub_const _).congr_deriv ?_
  have hAA : A0 * A0 = Y θ₀ := CFC.sqrt_mul_sqrt_self _ (by
    have := (posDef_add_smul_one (hP θ₀) hη).posSemidef; exact this.nonneg)
  have h1 : (Y θ₀ * X).trace = (1 / 2 : ℂ) * (A0 * P').trace := by
    have e : (A0 * P').trace = (A0 * (A0 * X + X * A0)).trace := by rw [hXs]
    have e2 : (A0 * (X * A0)).trace = (A0 * A0 * X).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [e, Matrix.mul_add, Matrix.trace_add, e2, ← Matrix.mul_assoc, ← hAA]
    ring
  rw [Matrix.trace_add, h1, Matrix.trace_mul_comm P']
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring
end Auto
