-- Prove2me | Definitions.Def_ExpChaotic_Results
-- name    : ExpChaotic_Results
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:01:25.433844+00:00
-- url     : https://prove2.me/theorems/50645fe9-7173-58d5-8dba-6151d5d7193d
-- title:
--   Results
-- statement:
--   Definitions and structural lemmas for Results, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Definitions.Def_ExpChaotic_Normality
import Definitions.Def_ExpChaotic_PaperConsequences
import Definitions.Def_ExpChaotic_Spherical
set_option autoImplicit true
open Function Filter Set Metric
namespace ExpChaotic
noncomputable section
abbrev expIterate (n : ℕ) : ℂ → ℂ := Complex.exp^[n]
def EscapesToInfinity (z : ℂ) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → R ≤ ‖expIterate n z‖)
def escapingSet : Set ℂ := {z | EscapesToInfinity z}
def denseOrbitSet : Set ℂ :=
  {z | Dense (MulAction.orbit (IterateMulAct Complex.exp) z)}
def repellingPeriodicSet : Set ℂ :=
  {p | ∃ n : ℕ, 0 < n ∧ IsPeriodicPt Complex.exp n p ∧
    1 < ‖deriv (expIterate n) p‖}
abbrev RiemannSphere := OnePoint ℂ
instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    IsNormalSequenceOn (fun n z => ((f^[n]) z : RiemannSphere)) U}
def juliaSet (f : ℂ → ℂ) : Set ℂ := (fatouSet f)ᶜ
def IsDevaneyChaotic (f : ℂ → ℂ) : Prop :=
  Continuous f ∧ Dense (Function.periodicPts f) ∧
    MulAction.IsTopologicallyTransitive (IterateMulAct f) ℂ
def sphericalExpIterate (n : ℕ) (z : ℂ) : RiemannSphere :=
  (expIterate n z : OnePoint ℂ)
end
end ExpChaotic


