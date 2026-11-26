-- Prove2me | Definitions.Def_ExpChaotic_Spherical
-- name    : ExpChaotic_Spherical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:08.071806+00:00
-- url     : https://prove2.me/theorems/cb5b4fb2-ae2f-4ec6-85df-b396c5e7d1ea
-- title:
--   Spherical
-- statement:
--   Definitions and structural lemmas for Spherical, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
abbrev RiemannSphere := OnePoint ℂ
instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1
def riemannSphereUniformEquivUnitSphere :
    RiemannSphere ≃ᵤ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let e : RiemannSphere ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  exact
    { e.toEquiv with
      uniformContinuous_toFun := CompactSpace.uniformContinuous_of_continuous e.continuous
      uniformContinuous_invFun := CompactSpace.uniformContinuous_of_continuous e.symm.continuous }
def sphericalExpIterate (n : ℕ) (z : ℂ) : RiemannSphere :=
  (expIterate n z : OnePoint ℂ)
def HasSensitiveDependenceVia {Y : Type*} [MetricSpace Y] (q : ℂ → Y) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set ℂ, IsOpen U → U.Nonempty →
    ∃ n : ℕ, ∃ z ∈ U, ∃ w ∈ U,
      δ ≤ dist (q (expIterate n z)) (q (expIterate n w))
end
end ExponentialJuliaSetMisiurewicz


