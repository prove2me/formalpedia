-- Prove2me | Definitions.Def_Esgk_Energy
-- name    : Esgk_Energy
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:47.09921+00:00
-- url     : https://prove2.me/theorems/173e0d0a-7578-4bc5-98f4-33196ae395aa
-- title:
--   Distinct distance values of a finite configuration
-- statement:
--   This defines the distance values arising from ordered pairs of distinct indices in a finite indexed configuration and their cardinality. The definition does not require the indexed points to be distinct.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlanarGeneralPosition
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

 
noncomputable def OrderedDistanceValues {n : ℕ} (p : Config n) : Finset ℝ := Finset.image (fun ij : Fin n × Fin n ↦ dist (p ij.1) (p ij.2))
    ((Finset.univ.product Finset.univ).filter (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2))


noncomputable def NumDistances {n : ℕ} (p : Config n) : ℕ := EuclideanGeometry.distinctDistances (Config.toFinset p)

 
noncomputable def NumDistancesOrdered {n : ℕ} (p : Config n) : ℕ := (OrderedDistanceValues p).card


end Esgk


