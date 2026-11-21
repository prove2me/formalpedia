-- Prove2me | Definitions.Def_SourceProof_1ef3cd2b70d61f5d3e313bb1
-- name    : SourceProof_1ef3cd2b70d61f5d3e313bb1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:21:40.336555+00:00
-- url     : https://prove2.me/theorems/8c12ee39-c929-4eb2-84c0-f38f355d5e71
-- title:
--   LevyStochCalc source module: SourceProof_1ef3cd2b70d61f5d3e313bb1
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.toReal_density_apply` comes from the `LevyStochCalc.BSDEJ.PicardContractionNorm` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

variable [SigmaFinite ν]

omit [MeasurableSpace Ω] [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_1ef3cd2b70d61f5d3e313bb1 {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    {ω : Ω} {s : ℝ} (hU : ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    (density ν Y Z U ω s).toReal
      = (Y s ω) ^ 2 + (∑ j, (Z s ω j) ^ 2) + (∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
  classical
  have hsq : ∀ a : ℝ, ((‖a‖₊ : ℝ≥0∞) ^ 2).toReal = a ^ 2 := by
    intro a
    rw [← ENNReal.coe_pow, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
      sq_abs]
  have hfinA : ((‖Y s ω‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := by finiteness
  have hfinB : ∀ j : Fin d, ((‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := fun j => by finiteness
  have hfinS : (∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => hfinB j
  rw [LevyStochCalc.BSDEJ.Solves.density, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinA, hfinS⟩) hU,
    ENNReal.toReal_add hfinA hfinS, ENNReal.toReal_sum fun j _ => hfinB j]
  simp only [hsq]
end Norm

end LevyStochCalc.BSDEJ.Solves


