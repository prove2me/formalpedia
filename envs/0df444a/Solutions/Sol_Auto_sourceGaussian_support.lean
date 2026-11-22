-- Prove2me | solution 1 for Auto.sourceGaussian_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:40:51.516001+00:00
-- url     : https://prove2.me/submissions/153796ae-1ee3-4f68-a5c7-e220b73eb1c3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (F : Fin 3 → ℝ × ℝ → ℂ) {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    (x : Fin 3 → ℝ) (hx : ρ < ‖x‖) :
    sourceGaussianIntegrand F a b x = 0 := by
  by_cases h0 : F 0 (x 0, x 1) = 0
  · simp [sourceGaussianIntegrand, h0]
  by_cases h1 : F 1 (x 1, x 2) = 0
  · simp [sourceGaussianIntegrand, h1]
  have hp : ‖(x 0, x 1)‖ ≤ ρ := not_lt.1 fun h => h0 (hF 0 _ h)
  have hq : ‖(x 1, x 2)‖ ≤ ρ := not_lt.1 fun h => h1 (hF 1 _ h)
  rw [Prod.norm_def, max_le_iff] at hp hq
  have : ‖x‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ).2 (by
    intro i
    fin_cases i
    · exact hp.1
    · exact hp.2
    · exact hq.2)
  exact False.elim (not_lt_of_ge this hx)
end Auto
