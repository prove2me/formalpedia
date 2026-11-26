-- Prove2me | Definitions.Def_ExpChaotic_Dynamics
-- name    : ExpChaotic_Dynamics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:26.210802+00:00
-- url     : https://prove2.me/theorems/db4a7e6d-843a-4cc9-ba48-1bcfc2262598
-- title:
--   Dynamics
-- statement:
--   Definitions and structural lemmas for Dynamics, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_ExpChaotic_Periodic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
def EscapesToInfinity (z : ℂ) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, R ≤ ‖expIterate n z‖
def escapingSetExp : Set ℂ := {z | EscapesToInfinity z}
def orbitVisitSet (U : Set ℂ) : Set ℂ :=
  ⋃ n : ℕ, expIterate n ⁻¹' U
def denseOrbitSetExp : Set ℂ :=
  {z | Dense (MulAction.orbit (IterateMulAct Complex.exp) z)}
def IsDevaneyChaotic (f : ℂ → ℂ) : Prop :=
  Continuous f ∧ Dense (Function.periodicPts f) ∧
    MulAction.IsTopologicallyTransitive (IterateMulAct f) ℂ
end
end ExponentialJuliaSetMisiurewicz


