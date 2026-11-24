-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:43.483678+00:00
-- url     : https://prove2.me/theorems/3e97af37-6c74-472a-9c46-54c4d4bb4d25
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace EisTube
variable {ι : Type}
def reV (z : ι → ℂ) : ι → ℝ := fun i => (z i).re
def imV (z : ι → ℂ) : ι → ℝ := fun i => (z i).im
def tube (Ω : Set (ι → ℝ)) : Set (ι → ℂ) := {z | reV z ∈ Ω}
def farCone {J : Type*} [Fintype ι] (a : J → ι → ℝ) (R : ℝ) : Set (ι → ℝ) :=
  {x | ∀ j, R < ∑ i, x i * a j i}
def TubeExtends [Fintype ι] (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] : Prop :=
  ∀ (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
  (∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂) →
  ∀ (h : P → ℝ), (∀ p, 0 ≤ h p) → (∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) →
  ∀ (F : (ι → ℂ) → P → ℂ),
  (∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) →
  (∀ z ∈ tube Ω, Continuous (F z)) →
  (∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) →
  ∃ G : (ι → ℂ) → P → ℂ,
    (∀ p, Differentiable ℂ (fun z => G z p)) ∧
    (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
    Continuous (Function.uncurry G) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p)
end EisTube


