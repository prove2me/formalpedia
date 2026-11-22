-- Prove2me | solution 1 for Auto.hasDerivAt_energy_hessian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:16:48.547913+00:00
-- url     : https://prove2.me/submissions/ae45c2e0-eda9-441a-99c7-3e4154d15dd8

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_sqrt_curve
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_add_smul_one_sub_posSemidef
public import Theorems.Thm_Auto_hasDerivAt_re_trace_mul
public import Theorems.Thm_Auto_re_trace_sylvSol_mul

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
theorem _root_.solution {P G : ℝ → Matrix n n ℂ} {P' G' : Matrix n n ℂ} {θ₀ η : ℝ}
    (hη : 0 < η) (hP : ∀ θ, (P θ).PosSemidef)
    (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) (hGH : (G θ₀).IsHermitian) :
    HasDerivAt (fun θ => (3 / 2) * ((CFC.sqrt (P θ + (η : ℂ) • 1) * G θ).trace).re) (matCostBil
      (P θ₀ + (η : ℂ) • 1) P' (G θ₀) + (3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) * G').trace).re)
      θ₀ := by
  set Y : ℝ → Matrix n n ℂ := fun θ => P θ + (η : ℂ) • 1
  have hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (P' i j) θ₀ := by
    intro i j
    have := (hd i j).add_const (((η : ℂ) • (1 : Matrix n n ℂ)) i j)
    simpa [Y] using this
  have hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := fun θ =>
    add_smul_one_sub_posSemidef (hP θ) η
  have hA := hasDerivAt_sqrt_curve hη hpos hY
  have hT := (hasDerivAt_re_trace_mul hA hG).const_mul (3 / 2 : ℝ)
  refine hT.congr_deriv ?_
  rw [Matrix.trace_add, Complex.add_re, mul_add,
    re_trace_sylvSol_mul (posDef_add_smul_one (hP θ₀) hη) hGH]
end Auto
