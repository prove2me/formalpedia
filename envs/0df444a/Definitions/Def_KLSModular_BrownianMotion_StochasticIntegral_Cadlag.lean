-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Cadlag
-- name    : KLSModular_BrownianMotion_StochasticIntegral_Cadlag
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:46:23.400758+00:00
-- url     : https://prove2.me/theorems/018dc80a-f371-45a4-ad73-e4ef0a7c732d
-- title:
--   Càdlàg path predicates
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `IsRightContinuous` means that a function is continuous within the strict right neighborhood at every point. `IsCadlag` is a structure requiring right continuity together with existence of a left limit at every point, expressed by a filter `Tendsto` statement.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Analysis.Normed.Group.Continuity
--   public import Mathlib.Topology.Algebra.MulAction
--   public import Mathlib.Topology.Instances.ENNReal.Lemmas
--   public import Mathlib.Topology.MetricSpace.Bounded
--   public import Mathlib.Topology.Order.Compact
--   public import Mathlib.Topology.Order.LeftRightLim
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
--     ∀ a, ContinuousWithinAt f (Set.Ioi a) a
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/StochasticIntegral/Cadlag.lean) · `BrownianMotion.StochasticIntegral.Cadlag` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/Cadlag.lean#L26-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.Cadlag`, definition bundle `KLSModular_BrownianMotion_StochasticIntegral_Cadlag`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/StochasticIntegral/Cadlag.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open Filter TopologicalSpace Bornology
open scoped Topology ENNReal
variable {ι E : Type*} [TopologicalSpace ι]
/-- The predicate that a function is right continuous. -/
abbrev IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a
/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [TopologicalSpace E] [Preorder ι] (f : ι → E) : Prop where
  right_continuous : IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)


