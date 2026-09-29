-- Prove2me | Definitions.Def_Esgk_PlanarGeneralPosition
-- name    : Esgk_PlanarGeneralPosition
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-12T19:19:39.705439+00:00
-- url     : https://prove2.me/theorems/d19f5f20-6de3-4254-9c5e-9a1f227e0598
-- title:
--   Planar general position and distinct Euclidean distances
-- statement:
--   Defines the Euclidean plane, a predicate excluding three collinear points, the number of distinct values of `dist` on pairs of different points, and full general position requiring both no three collinear and no four cocircular points.
-- source:
--   Self-contained formal statement prepared for this mission.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Planar general-position primitives

Self-contained definitions used by the distinct-distances mission.
-/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Set

variable {α : Type*}

/-- A ternary relation holds for every three pairwise-distinct members of a set. -/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

open scoped EuclideanGeometry Finset

namespace EuclideanGeometry

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- No three distinct points of `A` are collinear. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- The number of distances occurring between distinct points of a finite planar set. -/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  #(points.offDiag.image fun pair : ℝ² × ℝ² => dist pair.1 pair.2)

/-- No three points are collinear and no four points are cocircular. -/
def InGeneralPosition (X : Finset ℝ²) : Prop :=
  NonTrilinear (SetLike.coe X) ∧
    ∀ T ⊆ X, #T = 4 → ¬Cospherical (SetLike.coe T)

end EuclideanGeometry


