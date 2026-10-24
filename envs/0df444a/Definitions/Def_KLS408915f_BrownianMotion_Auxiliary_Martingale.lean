-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Martingale
-- name    : KLS408915f_BrownianMotion_Auxiliary_Martingale
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:37:27.457422+00:00
-- url     : https://prove2.me/theorems/42803f6a-7d6c-4a45-910d-8fdcb33e0c5f
-- title:
--   Martingale reindexing by a monotone map
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `Martingale.indexComap` states that if $X$ is a martingale for a filtration $\mathcal F$, then $X\circ f$ is a martingale for `𝓕.indexComap hf` whenever $f$ is monotone. The result preserves the original measure and uses the reindexed filtration described by `Filtration.indexComap`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Martingale.lean#L58-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Martingale`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_Martingale`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Martingale.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace MeasureTheory
variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
section IndexComap
variable {ι' : Type*} [Preorder ι'] {f : ι' → ι}
/-- A martingale reindexed by a monotone map is a martingale for the reindexed filtration. -/
lemma Martingale.indexComap (hX : Martingale X 𝓕 P) (hf : Monotone f) :
    Martingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.condExp_ae_eq (hf hij)⟩
end IndexComap
end MeasureTheory


