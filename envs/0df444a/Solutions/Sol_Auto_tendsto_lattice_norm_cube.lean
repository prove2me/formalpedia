-- Prove2me | solution 1 for Auto.tendsto_lattice_norm_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:49.74194+00:00
-- url     : https://prove2.me/submissions/7b919e61-36c0-43f2-a285-b802575b8233

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_lattice_sampling_dominated_convergence
public import Theorems.Thm_Auto_exists_support_bound
public import Theorems.Thm_Auto_integral_fin2_eq

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
theorem _root_.solution {Φ : ℝ × ℝ → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2 * ∑' z : Fin 2 → ℤ, ‖Φ ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖
      ^ 3) atTop (𝓝 (∫ p, ‖Φ p‖ ^ 3)) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨ρ, hρ, hΦ⟩ := exists_support_bound hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h := lattice_sampling_dominated_convergence (d := 2)
    (fun x : Fin 2 → ℝ => ‖Φ (x 0, x 1)‖ ^ 3) ⟨C ^ 3, fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 3⟩
    ⟨ρ, fun x hx => by
      have : ρ < ‖(x 0, x 1)‖ := by
        by_contra hcon
        push Not at hcon
        rw [Prod.norm_def, max_le_iff] at hcon
        refine absurd hx (not_lt.2 ((pi_norm_le_iff_of_nonneg hρ).2 fun i => ?_))
        fin_cases i
        · exact hcon.1
        · exact hcon.2
      simp [hΦ _ this]⟩ ∅ (fun x _ => by fun_prop)
  rw [integral_fin2_eq (fun p => ‖Φ p‖ ^ 3)] at h
  simpa only [smul_eq_mul] using h
end Auto
