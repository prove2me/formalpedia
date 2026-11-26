-- Prove2me | Definitions.Def_ExpChaotic_StripGeometry
-- name    : ExpChaotic_StripGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:31.054625+00:00
-- url     : https://prove2.me/theorems/27c19d84-be2e-5ba8-98e9-597d9f510874
-- title:
--   Strip Geometry
-- statement:
--   Definitions and structural lemmas for Strip Geometry, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
def EventuallyMeetsNegativeRealAxis (V : Set ℂ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ V, (expIterate n z).im = 0 ∧ (expIterate n z).re < 0
def doubleStrip : Set ℂ :=
  {z | |z.im| ≤ 2 * Real.pi ∧ |(Complex.exp z).im| ≤ 2 * Real.pi}
def piStrip : Set ℂ := {z | |z.im| ≤ Real.pi}
def piDoubleStrip : Set ℂ :=
  {z | |z.im| ≤ Real.pi ∧ |(Complex.exp z).im| ≤ Real.pi}
end
end ExponentialJuliaSetMisiurewicz


