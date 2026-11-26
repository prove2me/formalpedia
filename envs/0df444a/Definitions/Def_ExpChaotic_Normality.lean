-- Prove2me | Definitions.Def_ExpChaotic_Normality
-- name    : ExpChaotic_Normality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:40.495015+00:00
-- url     : https://prove2.me/theorems/5a819df7-337d-4940-a2fc-f4058205e4b1
-- title:
--   Normality
-- statement:
--   Definitions and structural lemmas for Normality, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    IsNormalSequenceOn (fun n z => ((f^[n]) z : RiemannSphere)) U}
def juliaSet (f : ℂ → ℂ) : Set ℂ := (fatouSet f)ᶜ
end
end ExponentialJuliaSetMisiurewicz


