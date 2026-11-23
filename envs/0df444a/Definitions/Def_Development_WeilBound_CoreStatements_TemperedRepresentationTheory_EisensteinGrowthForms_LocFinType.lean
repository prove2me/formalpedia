-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_EisensteinGrowthForms_LocFinType
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_EisensteinGrowthForms_LocFinType
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:05.77681+00:00
-- url     : https://prove2.me/theorems/f97849b0-d670-4f46-9f6d-11c38d5a98f7
-- title:
--   Loc Fin Type
-- statement:
--   Definitions and structural lemmas for Loc Fin Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/EisensteinGrowthForms/LocFinType.lean

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
namespace SiegelEisensteinSeries
open Filter Topology
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U
def Separating (D : Set (E →ₗ[ℂ] ℂ)) : Prop :=
  ∀ v : E, v ≠ 0 → ∃ ν ∈ D, ν v ≠ 0
structure LinSys (E : Type*) [AddCommGroup E] [Module ℂ E] (I : Type*) where
  a : I → ℂ → E →ₗ[ℂ] ℂ
  c : I → ℂ → ℂ
variable {I : Type*}
def LinSys.Sol (Ξ : LinSys E I) (s : ℂ) : Set E := {v | ∀ i, Ξ.a i s v = Ξ.c i s}
def LinSys.FinTypeOn (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (W : Set ℂ) : Prop :=
  ∃ (k : ℕ) (Λ : ℂ → Fin k → E), (∀ j, WHolo D (fun s => Λ s j) W) ∧
    (∀ i j, DifferentiableOn ℂ (fun s => Ξ.a i s (Λ s j)) W) ∧
    ∀ s ∈ W, Ξ.Sol s ⊆ Submodule.span ℂ (Set.range (Λ s))
def LinSys.LocFinType (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (Ω : Set ℂ) : Prop :=
  ∀ s₀ ∈ Ω, ∃ W : Set ℂ, IsOpen W ∧ s₀ ∈ W ∧ W ⊆ Ω ∧ Ξ.FinTypeOn D W
end SiegelEisensteinSeries


