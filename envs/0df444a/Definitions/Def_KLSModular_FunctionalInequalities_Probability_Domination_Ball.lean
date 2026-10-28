-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Domination_Ball
-- name    : KLSModular_FunctionalInequalities_Probability_Domination_Ball
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:21:09.246373+00:00
-- url     : https://prove2.me/theorems/5559cbc8-8b2c-4b51-a4ac-b6b8f48d213b
-- title:
--   Measure domination from eventual small-ball estimates
-- statement:
--   `FunctionalInequalities.Probability.measure_le_smul_of_eventually_closedBall_le` states that, in a finite-dimensional real normed Borel space, if locally finite measures μ and m satisfy $\mu(\overline B(x,r))\le C\,m(\overline B(x,r))$ for all sufficiently small positive radii at every center, then $\mu\le C\,m$ as measures, with $C$ a nonnegative real constant. `absolutelyContinuous_of_eventually_closedBall_le` gives the corresponding absolute continuity conclusion $\mu\ll m$. The radius threshold may depend on the center, while the multiplier C is uniform.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   theorem measure_le_smul_of_eventually_closedBall_le (μ m : Measure E)
--       [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure m] (C : NNReal)
--       (h : ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
--         μ (closedBall x r) ≤ (C : ENNReal) * m (closedBall x r)) :
--       μ ≤ (C : ENNReal) • m
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Domination/Ball.lean) · `FunctionalInequalities.Probability.Domination.Ball` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Domination/Ball.lean#L20-L44 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Domination.Ball`, definition bundle `KLSModular_FunctionalInequalities_Probability_Domination_Ball`; the repository is private at upload time).

import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

noncomputable section
open MeasureTheory Filter Metric Topology
namespace FunctionalInequalities
namespace Probability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- A uniform finite bound on sufficiently small ball ratios implies domination on every
measurable set. The admissible radius may depend on the center. -/
theorem measure_le_smul_of_eventually_closedBall_le (μ m : Measure E)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure m] (C : NNReal)
    (h : ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (closedBall x r) ≤ (C : ENNReal) * m (closedBall x r)) :
    μ ≤ (C : ENNReal) • m := by
  have : IsLocallyFiniteMeasure ((C : ENNReal) • m) := by
    change IsLocallyFiniteMeasure (C • m)
    infer_instance
  apply Measure.le_iff.mpr
  intro s _
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le
    ((C : ENNReal) • m) Measure.AbsolutelyContinuous.rfl s
  intro x _
  apply (Besicovitch.tendsto_filterAt μ x).frequently
  exact (h x).mono (by intro r hr; simpa using hr) |>.frequently
/-- Small-ball domination supplies absolute continuity without assuming it in the covering
step. The Vitali family is built for the source measure itself. -/
theorem absolutelyContinuous_of_eventually_closedBall_le (μ m : Measure E)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure m] (C : NNReal)
    (h : ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (closedBall x r) ≤ (C : ENNReal) * m (closedBall x r)) : μ ≪ m :=
  Measure.absolutelyContinuous_of_le_smul (measure_le_smul_of_eventually_closedBall_le μ m C h)
end Probability
end FunctionalInequalities


