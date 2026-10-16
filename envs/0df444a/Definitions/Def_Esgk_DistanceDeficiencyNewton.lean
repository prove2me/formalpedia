-- Prove2me | Definitions.Def_Esgk_DistanceDeficiencyNewton
-- name    : Esgk_DistanceDeficiencyNewton
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:47.818838+00:00
-- url     : https://prove2.me/theorems/7ebb20b9-3d8c-41b2-8788-83bad7ebbe6d
-- title:
--   Missing distance multiplicities and power sums
-- statement:
--   For each point of a finite configuration, this defines the missing neighbor multiplicity at each ordered distance, the total missing degree, and the ordinary and missing power sums of squared distances.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
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

variable {n : ℕ}

 
noncomputable def DistanceMissingMultiplicity
    (p : Config n) (i : Fin n) (r : ℝ) : ℕ :=
  3 - (DistanceOutNeighborsAtValue p i r).card

 
noncomputable def DistanceMissingDegree (p : Config n) (i : Fin n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p, DistanceMissingMultiplicity p i r

 
noncomputable def DistanceSquaredProfilePowerSum
    (p : Config n) (i : Fin n) (j : ℕ) : ℝ :=
  ∑ r ∈ OrderedDistanceValues p,
    ((DistanceOutNeighborsAtValue p i r).card : ℝ) * (r ^ 2) ^ j

 
noncomputable def DistanceSquaredMissingPowerSum
    (p : Config n) (i : Fin n) (j : ℕ) : ℝ :=
  ∑ r ∈ OrderedDistanceValues p,
    (DistanceMissingMultiplicity p i r : ℝ) * (r ^ 2) ^ j


end Esgk


