-- Prove2me | Definitions.Def_Esgk_DistanceDesign
-- name    : Esgk_DistanceDesign
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:09.983691+00:00
-- url     : https://prove2.me/theorems/473178b9-1284-4c4c-a3ff-1f439f73c6e8
-- title:
--   Neighbors at a specified distance
-- statement:
--   This defines the finite set of indices different from a given index whose configuration points lie at a specified Euclidean distance from it.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_Foundation
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ} {α : Type*}


noncomputable def DistanceOutNeighborsAtValue {n : ℕ} (p : Config n) (i : Fin n) (r : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => i ≠ j ∧ dist (p i) (p j) = r)


end Esgk


