-- Prove2me | solution 1 for Arxiv2012_05254.npc_position_error
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:56:34.057869+00:00
-- url     : https://prove2.me/submissions/94116cfe-07e8-458d-9351-d54d1042c3a3

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

open Arxiv2012_05254 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u : Plane) (hu : u ≠ 0) (ψ : Ω → ℝ) (hψ : MemLp ψ 2 P) :
    Real.sqrt (variance (fun ω => perpOffset u (ψ ω)) P) =
      Real.sqrt (variance ψ P) / (2 * Real.pi * ‖u‖) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hc : 0 < 2 * Real.pi * ‖u‖ := by positivity
  have e : (fun ω => perpOffset u (ψ ω)) = fun ω => (2 * Real.pi * ‖u‖)⁻¹ * ψ ω := by
    funext ω; simp only [perpOffset]; ring
  rw [e, variance_const_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  field_simp
