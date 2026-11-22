-- Prove2me | Definitions.Def_SourceProof_aef3a69ee291c75edeeec8a2
-- name    : SourceProof_aef3a69ee291c75edeeec8a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:09:06.728587+00:00
-- url     : https://prove2.me/theorems/cf6fe9dc-4553-43dc-9016-bbaeee301cc5
-- title:
--   LevyStochCalc source module: SourceProof_aef3a69ee291c75edeeec8a2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_forall_integrableOn_windowLeftAt` comes from the `LevyStochCalc.Ito.JumpSplittingPathSums` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pathwise left-limit jump sums and compensator drifts

A pathwise jump sum is an integral against the random measure of a jump coefficient read along
the left limits of a path, so it is determined by a coefficient bundle, a random measure and a
path; no relation between the bundle and the path enters. This file indexes the left limits, the
left-limit jump sum over a mark set and the drift carrying the left-limit compensator on such a
triple, identifies them along the path of a jump diffusion with the jump-diffusion-indexed
objects, and records their elementary regularity: the jump sum vanishes over the degenerate
window, the jump sum and the compensator drift are unchanged when the left-limit jump integrand
is replaced by its zero extension, a càdlàg path meets its left limits at all but countably many
positive times, the jump sum is right-continuous in time, its integrand is almost surely
integrable over every bounded window of a mark set of finite intensity, and both the jump sum and
the compensator drift depend on the coefficient bundle only through the values of its jump
coefficient on that mark set.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}

section BarePath

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end BarePath

section BareRegularity

variable (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)

variable {Xp}

variable (Xp)


theorem _root_.Prove2MeSourceProof.h_aef3a69ee291c75edeeec8a2 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) := by
  have hstep : ∀ (m : ℕ) (i : Fin n), ∀ᵐ ω ∂P,
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) ((m : ℝ) + 1) ×ˢ A) (N.N ω) := by
    intro m i
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    filter_upwards [LevyStochCalc.Ito.JumpFormula.ae_integrableOn_window_of_zeroExtPos N hℱN hA hAν ((m : ℝ) + 1)
      (hpredL i) (hγmL i)
      (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
        (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i) (hγmL i) (hγqL i)
        (A := A) hpos)] with ω hω
    exact hω.1
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun m : ℕ =>
    MeasureTheory.ae_all_iff.mpr fun i : Fin n => hstep m i] with ω hω
  intro T i
  obtain ⟨m, hm⟩ := exists_nat_ge T
  refine (hω m i).mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) (subset_refl A))
  linarith
end BareRegularity

section Bundles

end Bundles

end Setup

end LevyStochCalc.Ito.JumpSplitting


