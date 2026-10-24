-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
-- name    : KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:37:46.995935+00:00
-- url     : https://prove2.me/theorems/124428c9-4324-42ab-b1d9-865aa9a32d4e
-- title:
--   Càdlàg path predicates
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `IsRightContinuous` means that a function is continuous within the strict right neighborhood at every point. `IsCadlag` is a structure requiring right continuity together with existence of a left limit at every point, expressed by a filter `Tendsto` statement.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/Cadlag.lean#L26-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.Cadlag`, definition bundle `KLS408915f_BrownianMotion_StochasticIntegral_Cadlag`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


