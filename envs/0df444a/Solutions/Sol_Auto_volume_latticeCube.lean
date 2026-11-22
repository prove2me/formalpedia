-- Prove2me | solution 1 for Auto.volume_latticeCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:32.765456+00:00
-- url     : https://prove2.me/submissions/97c6b282-8d27-4129-8660-e61e384e58bd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Auto
theorem _root_.solution {N : ℕ} (hN : 0 < N) (k : Fin d → ℤ) :
    volume (latticeCube N k) = ENNReal.ofReal ((N : ℝ)⁻¹) ^ d := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [latticeCube, Real.volume_pi_Ico]
  have : ∀ i, ((k i : ℝ) + 1) / N - (k i : ℝ) / N = (N : ℝ)⁻¹ := by
    intro i; field_simp; ring
  simp_rw [this]
  simp
end Auto
