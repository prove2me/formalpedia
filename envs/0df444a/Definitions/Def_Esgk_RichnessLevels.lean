-- Prove2me | Definitions.Def_Esgk_RichnessLevels
-- name    : Esgk_RichnessLevels
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:43.27246+00:00
-- url     : https://prove2.me/theorems/7265930b-22ac-4fff-884c-f25999582a14
-- title:
--   Orientation-preserving plane isometries
-- statement:
--   This defines a direct Euclidean plane isometry by positivity of the determinant of its linear part and supplies a decidability instance for that predicate.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlanarGeneralPosition
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Isometry

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise


noncomputable def IsDirect (g : IsometryEquiv ℝ² ℝ²) : Prop :=
  0 < LinearMap.det
    (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²)

 
noncomputable instance instDecidableIsDirect (g : IsometryEquiv ℝ² ℝ²) : Decidable (IsDirect g) := by
  unfold IsDirect; infer_instance


end Esgk


