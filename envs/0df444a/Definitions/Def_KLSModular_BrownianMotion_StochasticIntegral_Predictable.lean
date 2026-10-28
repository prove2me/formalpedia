-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Predictable
-- name    : KLSModular_BrownianMotion_StochasticIntegral_Predictable
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:46:38.249255+00:00
-- url     : https://prove2.me/theorems/8e95b9f6-de16-4b50-a1bf-65e43acaf5fa
-- title:
--   Completeness of a filtration
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `Filtration.IsComplete 𝓕 μ` requires every $\mu$-null set to be measurable in every sigma-algebra `𝓕 t`. The bundle also provides the induced instance asserting that each trimmed filtration `μ.trim (𝓕.le i)` is complete when the original filtration is complete.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.MeasureTheory.SetSemiring
--   public import Mathlib.Probability.Process.Adapted
--   public import Mathlib.Probability.Process.Filtration
--   public import Mathlib.Probability.Process.Predictable
--   public import Mathlib.Probability.Process.Stopping
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   class IsComplete (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac) where
--       /-- `𝓕 ⊥` contains all the null sets. -/
--       measurableSet_of_null ⦃s : Set Ω⦄ (hs : μ s = 0) (t : ι) : MeasurableSet[𝓕 t] s
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/StochasticIntegral/Predictable.lean) · `BrownianMotion.StochasticIntegral.Predictable` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/Predictable.lean#L326-L334 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.Predictable`, definition bundle `KLSModular_BrownianMotion_StochasticIntegral_Predictable`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Greg Neustroev, Shehzad Hathi
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/StochasticIntegral/Predictable.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open Filter Function MeasureTheory Order Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace MeasureTheory
namespace Filtration
variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E] [PartialOrder ι]
/-- A filtration `𝓕` is complete with respect to a measure `μ` if for all `i`, `𝓕 i` contains all
the `μ`-null sets. -/
class IsComplete (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac) where
    /-- `𝓕 ⊥` contains all the null sets. -/
    measurableSet_of_null ⦃s : Set Ω⦄ (hs : μ s = 0) (t : ι) : MeasurableSet[𝓕 t] s
instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : IsComplete 𝓕 μ] {i : ι} :
    (μ.trim <| 𝓕.le i).IsComplete :=
  ⟨fun _ hs ↦ IsComplete.measurableSet_of_null (measure_eq_zero_of_trim_eq_zero (𝓕.le i) hs) i⟩
variable {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] [OrderBot ι]
end Filtration
end MeasureTheory


