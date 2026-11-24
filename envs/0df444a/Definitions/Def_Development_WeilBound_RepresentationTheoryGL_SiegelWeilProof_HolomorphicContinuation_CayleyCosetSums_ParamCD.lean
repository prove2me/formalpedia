-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:42.359796+00:00
-- url     : https://prove2.me/theorems/b818093b-013c-43ab-84be-753c0ebe1530
-- title:
--   Param CD
-- statement:
--   Definitions and structural lemmas for Param CD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
structure Good {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set F) (K : F → X → E) : Prop where
  smooth : ∀ u, ContDiffOn ℝ ∞ (K · u) Ω
  cont : ∀ N : ℕ, ContinuousOn (fun p : F × X => iteratedFDeriv ℝ N (K · p.2) p.1) (Ω ×ˢ univ)
  supp : ∀ x ∈ Ω, ∃ V : Set F, IsOpen V ∧ x ∈ V ∧ ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ V, ∀ u ∉ C, K x' u = 0
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
section Kernel
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}
end Kernel
end PositivityTheory.Rg.Sw.HSt.PCD


