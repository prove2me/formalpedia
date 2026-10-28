-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
-- name    : KLSModular_FunctionalInequalities_Probability_LogConcave
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:36.178821+00:00
-- url     : https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b
-- title:
--   Compact-set log-concavity of probability measures
-- statement:
--   `FunctionalInequalities.KLS.LogConcave` says that a probability measure μ on a real normed Borel space is log-concave when, for compact sets K₀ and K₁ and every t with 0 < t < 1, $\mu(K₀)^t\mu(K₁)^{1-t}$ is at most the measure of their affine combination $\{tx+(1-t)y:x\in K₀,y\in K₁\}$. The definition allows measures supported on proper affine subspaces and includes no density, moment, nondegeneracy, or Poincaré assumption.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Normed.Module.Basic
--   import Mathlib.Analysis.SpecialFunctions.Pow.Real
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def LogConcave (μ : ProbabilityMeasure E) : Prop :=
--     ∀ (K₀ K₁ : Set E), IsCompact K₀ → IsCompact K₁ →
--       ∀ t : ℝ, 0 < t → t < 1 →
--         (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
--           (μ : Measure E) {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/LogConcave.lean) · `FunctionalInequalities.Probability.LogConcave` · Frozen source `408915f`.
-- source:
--   Source: Guédon–Milman, Interpolating thin-shell and sharp large-deviation estimates for isotropic log-concave measures (arXiv:1011.0943v3), item DLC; Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), item DLC. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/LogConcave.lean#L26-L32 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.LogConcave`, definition bundle `KLSModular_FunctionalInequalities_Probability_LogConcave`; the repository is private at upload time).

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FunctionalInequalities
namespace KLS
section LogConcavity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Compact-set log-concavity, including measures on proper affine supports.
The displayed combination of compact sets is compact in every real normed space. -/
def LogConcave (μ : ProbabilityMeasure E) : Prop :=
  ∀ (K₀ K₁ : Set E), IsCompact K₀ → IsCompact K₁ →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
        (μ : Measure E) {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}
end LogConcavity
end KLS
end FunctionalInequalities


