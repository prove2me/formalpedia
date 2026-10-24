-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:26:20.068954+00:00
-- url     : https://prove2.me/theorems/48a0a8e7-2ae7-4e57-b0db-3c6ae6a6bb8d
-- title:
--   Compact log-concavity from a Borell density
-- statement:
--   `IsBorellDensity.compactLogConcave` states that a finite-dimensional probability measure on an inner-product space with a pointwise log-concave Borell density relative to volume satisfies `LogConcave` on compact sets. The density may vanish, so positivity everywhere is not assumed; the result is an application of the finite-dimensional Prékopa–Leindler inequality.
-- source:
--   Source: Guédon–Milman, Interpolating thin-shell and sharp large-deviation estimates for isotropic log-concave measures (arXiv:1011.0943v3), item DLC. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/FromBorell.lean#L22-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.FromBorell`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace FunctionalInequalities
namespace KLS
namespace IsBorellDensity
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
/-- A probability law with a pointwise log-concave Borell density is log-concave
on compact sets. This does not require the density to be positive everywhere. -/
theorem compactLogConcave {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) : LogConcave ν := by
  intro K₀ K₁ hK₀ hK₁ t ht0 ht1
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  set C := {z : V | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} with hC
  have hCc : IsCompact C := isCompact_combination hK₀ hK₁ t
  have hmass : ∀ S : Set V, MeasurableSet S →
      (ν : Measure V) S = ∫⁻ x, ENNReal.ofReal (S.indicator ρ x) := by
    intro S hS
    have hind : ∀ x, ENNReal.ofReal (S.indicator ρ x) =
        S.indicator (fun y => ENNReal.ofReal (ρ y)) x := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    simp_rw [hind]
    rw [lintegral_indicator hS, ← hρ.withDensity_eq, withDensity_apply _ hS]
  rw [hmass K₀ hK₀.measurableSet, hmass K₁ hK₁.measurableSet,
    hmass C hCc.measurableSet]
  refine Analysis.prekopaLeindler (hρ.measurable.indicator hK₀.measurableSet)
    (hρ.measurable.indicator hK₁.measurableSet)
    (hρ.measurable.indicator hCc.measurableSet)
    (fun x => Set.indicator_nonneg (fun y _ => hρ.nonneg y) x)
    (fun y => Set.indicator_nonneg (fun z _ => hρ.nonneg z) y) ht0 ht1 ?_
  intro x y
  have hh0 : ∀ z, 0 ≤ C.indicator ρ z := fun z =>
    Set.indicator_nonneg (fun w _ => hρ.nonneg w) z
  by_cases hx : x ∈ K₀
  · by_cases hy : y ∈ K₁
    · have hz : t • x + (1 - t) • y ∈ C := ⟨x, hx, y, hy, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact hρ.logConcave x y t ht0 ht1
    · rw [Set.indicator_of_notMem hy, Real.zero_rpow ht1'.ne', mul_zero]
      exact hh0 _
  · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact hh0 _
end IsBorellDensity
end KLS
end FunctionalInequalities


